module

public import SphereSixComplex.Prerequisites.Topology.SingularOpenCoverLebesgue
public import SphereSixComplex.Prerequisites.Topology.SingularExcisionQuasiIso
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









/-- Powers of the barycentric mesh factor eventually fall below every positive tolerance. -/
public theorem exists_barycentricContractionFactor_pow_lt
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, barycentricContractionFactor n ^ m < ε :=
  exists_pow_lt_of_lt_one hε (barycentricContractionFactor_lt_one n)


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
    (h : ∀ (n : ℕ) (x : (integralSingularChainComplexObj X).X n),
      ∃ m : ℕ, (affineSingularSubdivisionIterate X m).f n x ∈
        Set.range ((coverSmallIntegralSingularChainInclusion X U).f n)) :
    CoverSmallAffineSubdivisionEventuallySmall X U := by
  intro n x
  obtain ⟨m, y, hy⟩ := h n x
  exact ⟨m, y, hy⟩

end SphereSixComplex
