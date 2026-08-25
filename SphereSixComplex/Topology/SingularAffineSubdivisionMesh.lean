module

public import SphereSixComplex.Topology.SingularOpenCoverLebesgue
public import SphereSixComplex.Topology.SingularExcisionQuasiIso
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Mesh estimates for affine barycentric subdivision

This file proves the quantitative geometric estimate behind the small-chain argument.  In the
sup metric on the standard `n`-simplex, the affine simplex associated to every flag of nonempty
faces has diameter at most `n / (n + 1)`.  The proof uses the exact face-barycenter coordinates
from `SingularAffineSubdivision`.

The final theorem packages the metric conclusion needed for iterated subdivision: any family of
nonempty cells whose diameters are bounded by successive powers of this factor is eventually
subordinate to an arbitrary open cover of a compact metric space.  Connecting that abstract
family to the chain-level iterate requires keeping the ancestry of every iterated affine flag;
that combinatorial bookkeeping is intentionally separate from the metric argument here.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits PartialOrder Set Simplicial

namespace SphereSixComplex

/-- The classical mesh-contraction factor for barycentric subdivision of an `n`-simplex. -/
public noncomputable def barycentricContractionFactor (n : ℕ) : ℝ :=
  (n : ℝ) / (n + 1)

public theorem barycentricContractionFactor_nonneg (n : ℕ) :
    0 ≤ barycentricContractionFactor n := by
  unfold barycentricContractionFactor
  positivity

public theorem barycentricContractionFactor_lt_one (n : ℕ) :
    barycentricContractionFactor n < 1 := by
  unfold barycentricContractionFactor
  rw [div_lt_one (by positivity)]
  norm_num

/-- The intrinsic diameter of a nonempty standard simplex is one in the sup metric. -/
public theorem diam_univ_stdSimplex (n : ℕ) (hn : 1 ≤ n) :
    Metric.diam (Set.univ : Set (stdSimplex ℝ (Fin (n + 1)))) = 1 := by
  let _ : Nontrivial (Fin (n + 1)) :=
    Fin.nontrivial_iff_two_le.mpr (Nat.add_le_add_right hn 1)
  calc
    Metric.diam (Set.univ : Set (stdSimplex ℝ (Fin (n + 1)))) =
        Metric.diam (Set.range
          (Subtype.val : stdSimplex ℝ (Fin (n + 1)) → Fin (n + 1) → ℝ)) :=
      isometry_subtype_coe.diam_range.symm
    _ = Metric.diam (stdSimplex ℝ (Fin (n + 1))) := by
      congr 1
      ext w
      simp
    _ = 1 := diam_stdSimplex

/-- Arithmetic estimate for barycenters of two nested nonempty faces. -/
public theorem inv_natCast_sub_inv_natCast_le_barycentricContractionFactor
    (n a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ n + 1) :
    |(a : ℝ)⁻¹ - (b : ℝ)⁻¹| ≤ barycentricContractionFactor n := by
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hbR : (b : ℝ) ≤ n + 1 := by exact_mod_cast hb
  have hB : (0 : ℝ) < b := lt_of_lt_of_le zero_lt_one (haR.trans habR)
  have h_inv_ab : (b : ℝ)⁻¹ ≤ (a : ℝ)⁻¹ :=
    inv_anti₀ (by positivity) habR
  rw [abs_of_nonneg (sub_nonneg.mpr h_inv_ab)]
  have ha_one : (a : ℝ)⁻¹ ≤ 1 := by
    simpa using (inv_anti₀ (by norm_num : (0 : ℝ) < 1) haR)
  have hb_N : (n + 1 : ℝ)⁻¹ ≤ (b : ℝ)⁻¹ :=
    inv_anti₀ hB hbR
  have hfactor : barycentricContractionFactor n =
      1 - (n + 1 : ℝ)⁻¹ := by
    unfold barycentricContractionFactor
    field_simp
    ring
  rw [hfactor]
  linarith

/-- If a face acquires a new vertex, then its barycenter coordinate at that vertex is bounded by
the barycentric mesh factor. -/
public theorem inv_natCast_le_barycentricContractionFactor_of_two_le
    (n b : ℕ) (hn : 1 ≤ n) (hb₂ : 2 ≤ b) :
    (b : ℝ)⁻¹ ≤ barycentricContractionFactor n := by
  have hb₂R : (2 : ℝ) ≤ b := by exact_mod_cast hb₂
  have hnR : (2 : ℝ) ≤ n + 1 := by
    exact_mod_cast (Nat.add_le_add_right hn 1)
  have hbhalf : (b : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ :=
    inv_anti₀ (by norm_num) hb₂R
  have hNhalf : (n + 1 : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ :=
    inv_anti₀ (by norm_num) hnR
  have hfactor : barycentricContractionFactor n =
      1 - (n + 1 : ℝ)⁻¹ := by
    unfold barycentricContractionFactor
    field_simp
    ring
  rw [hfactor]
  have hhalf : (2 : ℝ)⁻¹ ≤ 1 - (n + 1 : ℝ)⁻¹ := by
    norm_num at hNhalf ⊢
    linarith
  exact hbhalf.trans hhalf

/-- Barycenters of two nested nonempty faces of the standard `n`-simplex are at distance at
most `n / (n + 1)` in the sup metric. -/
public theorem dist_nonemptyFiniteChainBarycenter_le
    (n : ℕ) (hn : 1 ≤ n)
    (A B : NonemptyFiniteChains (ULift.{0} (Fin (n + 1)))) (hAB : A ≤ B) :
    dist (nonemptyFiniteChainBarycenter A)
      (nonemptyFiniteChainBarycenter B) ≤ barycentricContractionFactor n := by
  classical
  change dist (nonemptyFiniteChainBarycenter A : Fin (n + 1) → ℝ)
      (nonemptyFiniteChainBarycenter B : Fin (n + 1) → ℝ) ≤ _
  rw [dist_pi_le_iff (barycentricContractionFactor_nonneg n)]
  intro i
  rw [Real.dist_eq, nonemptyFiniteChainBarycenter_apply,
    nonemptyFiniteChainBarycenter_apply]
  by_cases hiA : ULift.up i ∈ A.finset
  · have hiB : ULift.up i ∈ B.finset := hAB hiA
    rw [ite_eq_left hiA, ite_eq_left hiB]
    apply inv_natCast_sub_inv_natCast_le_barycentricContractionFactor
    · exact A.nonempty.card_pos
    · exact Finset.card_le_card hAB
    · simpa using B.finset.card_le_univ
  · by_cases hiB : ULift.up i ∈ B.finset
    · rw [ite_eq_right hiA, ite_eq_left hiB, zero_sub, abs_neg,
        abs_of_nonneg (by positivity)]
      apply inv_natCast_le_barycentricContractionFactor_of_two_le n
        B.finset.card hn
      have hss : A.finset ⊂ B.finset :=
        Finset.ssubset_iff_subset_ne.mpr ⟨hAB, ?_⟩
      · exact (Finset.card_lt_card hss).trans_le' A.nonempty.card_pos
      · intro heq
        exact hiA (heq.symm ▸ hiB)
    · simp [hiA, hiB, barycentricContractionFactor_nonneg]

/-- The finite set of barycenters occurring as the vertices of an affine flag simplex. -/
public noncomputable def affineFlagVertexSet (n k : ℕ)
    (F : (SimplexCategory.sd.{0}.obj (SimplexCategory.mk n)).obj
      (Opposite.op (SimplexCategory.mk k))) :
    Set (Fin (n + 1) → ℝ) :=
  Set.range fun j ↦
    (nonemptyFiniteChainBarycenter (F.obj j) : Fin (n + 1) → ℝ)

/-- The vertices of any affine flag simplex satisfy the barycentric mesh estimate. -/
public theorem diam_affineFlagVertexSet_le
    (n k : ℕ) (hn : 1 ≤ n)
    (F : (SimplexCategory.sd.{0}.obj (SimplexCategory.mk n)).obj
      (Opposite.op (SimplexCategory.mk k))) :
    Metric.diam (affineFlagVertexSet n k F) ≤
      barycentricContractionFactor n := by
  apply Metric.diam_le_of_forall_dist_le
    (barycentricContractionFactor_nonneg n)
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  change dist (nonemptyFiniteChainBarycenter (F.obj i))
      (nonemptyFiniteChainBarycenter (F.obj j)) ≤ _
  rcases le_total i j with hij | hji
  · exact dist_nonemptyFiniteChainBarycenter_le n hn _ _
      (CategoryTheory.leOfHom (F.map (CategoryTheory.homOfLE hij)))
  · simpa [dist_comm] using
      dist_nonemptyFiniteChainBarycenter_le n hn _ _
        (CategoryTheory.leOfHom (F.map (CategoryTheory.homOfLE hji)))

/-- Every point of an affine flag simplex lies in the convex hull of its barycenter vertices. -/
public theorem affineFlagContinuousMap_mem_convexHull_vertices
    (n k : ℕ)
    (F : (SimplexCategory.sd.{0}.obj (SimplexCategory.mk n)).obj
      (Opposite.op (SimplexCategory.mk k)))
    (w : stdSimplex ℝ (Fin (k + 1))) :
    (affineFlagContinuousMap n k F w : Fin (n + 1) → ℝ) ∈
      convexHull ℝ (affineFlagVertexSet n k F) := by
  classical
  change (fun i ↦ ∑ j, w j * nonemptyFiniteChainBarycenter (F.obj j) i) ∈ _
  have hmem := (convex_convexHull ℝ (affineFlagVertexSet n k F)).sum_mem
    (t := Finset.univ) (w := fun j ↦ w j)
    (z := fun j ↦
      (nonemptyFiniteChainBarycenter (F.obj j) : Fin (n + 1) → ℝ))
    (fun j _ ↦ w.2.1 j) w.2.2 (fun j _ ↦
      subset_convexHull ℝ (affineFlagVertexSet n k F) ⟨j, rfl⟩)
  convert hmem using 1
  ext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- The image of every affine flag map contracts the mesh by the factor `n / (n + 1)`.  The
diameter is stated after the isometric inclusion into the ambient function space. -/
public theorem diam_range_affineFlagContinuousMap_coe_le
    (n k : ℕ) (hn : 1 ≤ n)
    (F : (SimplexCategory.sd.{0}.obj (SimplexCategory.mk n)).obj
      (Opposite.op (SimplexCategory.mk k))) :
    Metric.diam (Set.range fun w ↦
      (affineFlagContinuousMap n k F w : Fin (n + 1) → ℝ)) ≤
      barycentricContractionFactor n := by
  calc
    Metric.diam (Set.range fun w ↦
        (affineFlagContinuousMap n k F w : Fin (n + 1) → ℝ)) ≤
        Metric.diam (convexHull ℝ (affineFlagVertexSet n k F)) := by
      apply Metric.diam_mono
      · rintro _ ⟨w, rfl⟩
        exact affineFlagContinuousMap_mem_convexHull_vertices n k F w
      · rw [isBounded_convexHull]
        apply (bounded_stdSimplex (Fin (n + 1))).subset
        rintro _ ⟨j, rfl⟩
        exact (nonemptyFiniteChainBarycenter (F.obj j)).2
    _ = Metric.diam (affineFlagVertexSet n k F) := convexHull_diam _
    _ ≤ _ := diam_affineFlagVertexSet_le n k hn F

/-- Intrinsic version of the affine-flag mesh estimate. -/
public theorem diam_range_affineFlagContinuousMap_le
    (n k : ℕ) (hn : 1 ≤ n)
    (F : (SimplexCategory.sd.{0}.obj (SimplexCategory.mk n)).obj
      (Opposite.op (SimplexCategory.mk k))) :
    Metric.diam (Set.range (affineFlagContinuousMap n k F)) ≤
      barycentricContractionFactor n := by
  apply Metric.diam_le_of_forall_dist_le
    (barycentricContractionFactor_nonneg n)
  rintro _ ⟨w, rfl⟩ _ ⟨w', rfl⟩
  change dist
    (affineFlagContinuousMap n k F w : Fin (n + 1) → ℝ)
    (affineFlagContinuousMap n k F w' : Fin (n + 1) → ℝ) ≤ _
  exact Metric.dist_le_diam_of_mem
    (by
      rw [isBounded_convexHull]
      apply (bounded_stdSimplex (Fin (n + 1))).subset
      rintro _ ⟨j, rfl⟩
      exact (nonemptyFiniteChainBarycenter (F.obj j)).2)
    (affineFlagContinuousMap_mem_convexHull_vertices n k F w)
    (affineFlagContinuousMap_mem_convexHull_vertices n k F w') |>.trans
      (by rw [convexHull_diam]; exact diam_affineFlagVertexSet_le n k hn F)

/-- Powers of the barycentric mesh factor eventually fall below every positive tolerance. -/
public theorem exists_barycentricContractionFactor_pow_lt
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, barycentricContractionFactor n ^ m < ε :=
  exists_pow_lt_of_lt_one hε (barycentricContractionFactor_lt_one n)

/-- One actual affine flag cell in the subdivision of a singular simplex maps into a cover
member as soon as the barycentric contraction factor is below the pulled-back Lebesgue number.
This is the direct bridge between the metric estimate in this file and cover-smallness. -/
public theorem singularSimplex_affineFlag_image_subset_cover_of_factor_lt
    {ι : Type} (X : TopCat.{0}) (U : ι → Set X)
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ)
    (n : ℕ) (hn : 1 ≤ n)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)))
    (F : (SimplexCategory.sd.{0}.obj (SimplexCategory.mk n)).obj
      (Opposite.op (SimplexCategory.mk n))) :
    ∃ δ > 0, barycentricContractionFactor n < δ →
      ∃ i, X.toSSetObjEquiv _ x '' Set.range (affineFlagContinuousMap n n F) ⊆ U i := by
  let s : Set (stdSimplex ℝ (Fin (n + 1))) :=
    Set.range (affineFlagContinuousMap n n F)
  have hsne : s.Nonempty := Set.range_nonempty _
  have hsbounded : Bornology.IsBounded s :=
    isCompact_univ.isBounded.subset (Set.subset_univ s)
  obtain ⟨δ, hδ, hsmall⟩ := singularSimplex_image_subset_cover_of_diam_lt
    X U hUopen hUcover n x hsne hsbounded
  refine ⟨δ, hδ, fun hfactor ↦ hsmall ?_⟩
  exact (diam_range_affineFlagContinuousMap_le n n hn F).trans_lt hfactor

/-! ## Iterated affine-cell ancestry -/

/-- A top-dimensional flag in the barycentric subdivision of the standard `n`-simplex. -/
public abbrev TopAffineFlag (n : ℕ) :=
  (SimplexCategory.sd.{0}.obj (SimplexCategory.mk n)).obj
    (Opposite.op (SimplexCategory.mk n))

/-- The affine cell map described by a finite ancestry of top-dimensional flags.  The head of
the list is the newest (innermost) subdivision cell and the tail records its parent ancestry. -/
public noncomputable def iteratedAffineCellMap (n : ℕ)
    (ancestry : List (TopAffineFlag n)) :
    C(stdSimplex ℝ (Fin (n + 1)), stdSimplex ℝ (Fin (n + 1))) :=
  match ancestry with
  | [] => ContinuousMap.id _
  | F :: ancestry =>
      (iteratedAffineCellMap n ancestry).comp (affineFlagContinuousMap n n F)

@[simp]
public theorem iteratedAffineCellMap_nil (n : ℕ) :
    iteratedAffineCellMap n [] = ContinuousMap.id _ :=
  rfl

@[simp]
public theorem iteratedAffineCellMap_cons
    (n : ℕ) (F : TopAffineFlag n) (ancestry : List (TopAffineFlag n)) :
    iteratedAffineCellMap n (F :: ancestry) =
      (iteratedAffineCellMap n ancestry).comp
        (affineFlagContinuousMap n n F) :=
  rfl

/-- The exact relative contraction assertion needed to iterate the one-cell estimate.  It is
restricted to the explicitly affine parent maps built from flag ancestries: subdividing inside
such a parent cell multiplies that parent's diameter by at most the standard barycentric factor.
No assertion is made for arbitrary continuous parent maps. -/
public def AffineFlagRelativeMeshContraction (n : ℕ) : Prop :=
  ∀ (ancestry : List (TopAffineFlag n)) (F : TopAffineFlag n),
    Metric.diam (Set.range
      ((iteratedAffineCellMap n ancestry).comp
        (affineFlagContinuousMap n n F))) ≤
      barycentricContractionFactor n *
        Metric.diam (Set.range (iteratedAffineCellMap n ancestry))

/-- The proven one-step estimate is the root case of relative mesh contraction. -/
public theorem affineFlagRelativeMeshContraction_at_identity
    (n : ℕ) (hn : 1 ≤ n) (F : TopAffineFlag n) :
    Metric.diam (Set.range
      ((ContinuousMap.id _).comp (affineFlagContinuousMap n n F))) ≤
      barycentricContractionFactor n *
        Metric.diam (Set.range (ContinuousMap.id
          (stdSimplex ℝ (Fin (n + 1))))) := by
  have hid : Set.range (ContinuousMap.id
      (stdSimplex ℝ (Fin (n + 1)))) = Set.univ := by
    ext w
    simp
  rw [ContinuousMap.id_comp, hid, diam_univ_stdSimplex n hn, mul_one]
  exact diam_range_affineFlagContinuousMap_le n n hn F

/-- Under relative contraction, an affine cell at ancestry depth `m` has diameter at most the
`m`th power of the barycentric factor. -/
public theorem diam_range_iteratedAffineCellMap_le_pow
    (n : ℕ) (hn : 1 ≤ n) (hrelative : AffineFlagRelativeMeshContraction n)
    (ancestry : List (TopAffineFlag n)) :
    Metric.diam (Set.range (iteratedAffineCellMap n ancestry)) ≤
      barycentricContractionFactor n ^ ancestry.length := by
  induction ancestry with
  | nil =>
      rw [iteratedAffineCellMap_nil, List.length_nil, pow_zero]
      have hid : Set.range (ContinuousMap.id
          (stdSimplex ℝ (Fin (n + 1)))) = Set.univ := by
        ext w
        simp
      rw [hid, diam_univ_stdSimplex n hn]
  | cons F ancestry ih =>
      calc
        Metric.diam (Set.range (iteratedAffineCellMap n (F :: ancestry))) ≤
            barycentricContractionFactor n *
              Metric.diam (Set.range (iteratedAffineCellMap n ancestry)) := by
          simpa only [iteratedAffineCellMap_cons] using
            hrelative ancestry F
        _ ≤ barycentricContractionFactor n *
              barycentricContractionFactor n ^ ancestry.length :=
          mul_le_mul_of_nonneg_left ih (barycentricContractionFactor_nonneg n)
        _ = barycentricContractionFactor n ^ (F :: ancestry).length := by
          simp only [List.length_cons, pow_succ]
          ring

/-- Relative mesh contraction gives a common ancestry depth at which every iterated affine cell
of a fixed singular simplex is carried into one member of an arbitrary open cover. -/
public theorem exists_iteratedAffineCell_depth_subordinate
    {ι : Type} (X : TopCat.{0}) (U : ι → Set X)
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ)
    (n : ℕ) (hn : 1 ≤ n)
    (hrelative : AffineFlagRelativeMeshContraction n)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n))) :
    ∃ m : ℕ, ∀ ancestry : List (TopAffineFlag n), ancestry.length = m →
      ∃ i, X.toSSetObjEquiv _ x ''
        Set.range (iteratedAffineCellMap n ancestry) ⊆ U i := by
  obtain ⟨δ, hδ, hLeb⟩ :=
    singularSimplex_openCover_lebesgueNumber X U hUopen hUcover n x
  obtain ⟨m, hm⟩ := exists_barycentricContractionFactor_pow_lt n hδ
  refine ⟨m, fun ancestry hlength ↦ ?_⟩
  let s : Set (stdSimplex ℝ (Fin (n + 1))) :=
    Set.range (iteratedAffineCellMap n ancestry)
  let w₀ : stdSimplex ℝ (Fin (n + 1)) := Classical.arbitrary _
  obtain ⟨i, hi⟩ := hLeb (iteratedAffineCellMap n ancestry w₀)
  refine ⟨i, ?_⟩
  rintro _ ⟨y, ⟨w, rfl⟩, rfl⟩
  apply hi
  rw [Metric.mem_ball]
  have hsbounded : Bornology.IsBounded s :=
    isCompact_univ.isBounded.subset (Set.subset_univ s)
  exact (Metric.dist_le_diam_of_mem hsbounded
    (show iteratedAffineCellMap n ancestry w ∈ s from ⟨w, rfl⟩)
    (show iteratedAffineCellMap n ancestry w₀ ∈ s from ⟨w₀, rfl⟩)).trans_lt
      ((diam_range_iteratedAffineCellMap_le_pow n hn hrelative ancestry).trans_lt
        (hlength.symm ▸ hm))

/-- Abstract eventual-smallness theorem for iterated cells.  Once a concrete subdivision model
supplies nonempty cells with the displayed power-law diameter bound, a single depth works for all
cells and makes each of them lie in one member of any open cover. -/
public theorem exists_depth_for_diameter_controlled_cells_subordinate
    {X α ι : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (n : ℕ) (U : ι → Set X) (hUopen : ∀ i, IsOpen (U i))
    (hUcover : (Set.univ : Set X) ⊆ ⋃ i, U i)
    (cell : ℕ → α → Set X)
    (hcell : ∀ m a, (cell m a).Nonempty)
    (hdiam : ∀ m a, Metric.diam (cell m a) ≤
      barycentricContractionFactor n ^ m) :
    ∃ m : ℕ, ∀ a : α, ∃ i : ι, cell m a ⊆ U i := by
  obtain ⟨δ, hδ, hball⟩ :=
    lebesgue_number_lemma_of_metric isCompact_univ hUopen hUcover
  obtain ⟨m, hm⟩ := exists_barycentricContractionFactor_pow_lt n hδ
  refine ⟨m, fun a ↦ ?_⟩
  obtain ⟨x, hx⟩ := hcell m a
  obtain ⟨i, hi⟩ := hball x (Set.mem_univ x)
  refine ⟨i, fun y hy ↦ hi ?_⟩
  rw [Metric.mem_ball]
  exact (Metric.dist_le_diam_of_mem
    (isCompact_univ.isBounded.subset (Set.subset_univ _)) hy hx).trans_lt
      ((hdiam m a).trans_lt hm)

/-! ## Chain-level endpoint -/

/-- Iterating affine subdivision is additive in the exponent.  This synchronization identity is
the algebraic tool for putting finitely many generatorwise subdivision depths over one common
depth. -/
public theorem affineSingularSubdivisionIterate_add
    (X : TopCat) (m r : ℕ) :
    affineSingularSubdivisionIterate X (m + r) =
      affineSingularSubdivisionIterate X m ≫
        affineSingularSubdivisionIterate X r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Nat.add_succ, affineSingularSubdivisionIterate_succ, ih,
        affineSingularSubdivisionIterate_succ, Category.assoc]

/-- A sharply stated range bridge from geometry to the algebraic small-chain endpoint: it is
enough to prove that some affine-subdivision iterate of every chain lies in the degreewise range
of the cover-small inclusion. -/
public theorem coverSmallAffineSubdivisionEventuallySmall_of_iterate_mem_range
    {iota : Type} (X : TopCat) (U : iota → Set X)
    (h : ∀ (n : ℕ) (x : (IntegralSingularChainComplexObj X).X n),
      ∃ m : ℕ, (affineSingularSubdivisionIterate X m).f n x ∈
        Set.range ((coverSmallIntegralSingularChainInclusion X U).f n)) :
    CoverSmallAffineSubdivisionEventuallySmall X U := by
  intro n x
  obtain ⟨m, y, hy⟩ := h n x
  exact ⟨m, y, hy⟩

end SphereSixComplex
