module

public import DifferentialGeometry.Topology.Homology.Subdivision.UniversalGeometry
public import DifferentialGeometry.Topology.Homology.Subdivision.Mesh
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u

namespace DifferentialGeometry.Homology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {k : Type u} [Ring k] (R : ModuleCat.{u} k)

local notation "K" => _root_.SSet.chainComplex (TopCat.toSSet.obj (TopCat.of E)) R


def affineMeshSubmodule (s : Set E) (n : ℕ) (D : ℝ) : Submodule k ((K).X n) :=
  Submodule.span k {c | ∃ v : Fin (n + 1) → E, (∀ i, v i ∈ s) ∧
    (∀ i j, dist (v i) (v j) ≤ D) ∧ ∃ r : R,
      c = (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex (R := R) (affineSingularSimplex v) r}


theorem affineGenerator_mem_affineMeshSubmodule {s : Set E} {n : ℕ} {D : ℝ}
    (v : Fin (n + 1) → E) (hvs : ∀ i, v i ∈ s)
    (hvD : ∀ i j, dist (v i) (v j) ≤ D) (r : R) :
    (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex (R := R) (affineSingularSimplex v) r ∈
      affineMeshSubmodule R s n D :=
  Submodule.subset_span ⟨v, hvs, hvD, r, rfl⟩


theorem affineMeshSubmodule_le_comap_subdivision {s : Set E} (hs : Convex ℝ s)
    (n : ℕ) (D : ℝ) :
    affineMeshSubmodule R s n D ≤
      (affineMeshSubmodule R s n ((n : ℝ) / (n + 1) * D)).comap
        (singularSubdivisionMap R (TopCat.of E) n).hom := by
  apply Submodule.span_le.mpr
  rintro _ ⟨v, hvs, hvD, r, rfl⟩
  change (singularSubdivisionMap R (TopCat.of E) n)
    ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex (R := R) (affineSingularSimplex v) r) ∈
      affineMeshSubmodule R s n ((n : ℝ) / (n + 1) * D)
  have he := congrArg (fun f ↦ ModuleCat.Hom.hom f r)
    ((singularSubdivisionMap_affine R v).trans (affineSubdivisionMap_pieces R n v))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_sum,
    LinearMap.sum_apply, ModuleCat.hom_zsmul, LinearMap.smul_apply] at he
  rw [he]
  apply Submodule.sum_mem
  intro p _
  apply (affineMeshSubmodule R s n ((n : ℝ) / (n + 1) * D)).toAddSubgroup.zsmul_mem
  exact affineGenerator_mem_affineMeshSubmodule R (barycentricPieceVertices n v p)
    (barycentricPieceVertices_mem n v p hs hvs)
    (dist_barycentricPieceVertices_le n v p hvD) r


theorem singularSubdivision_pow_mem_affineMeshSubmodule {s : Set E} (hs : Convex ℝ s)
    (n m : ℕ) {D : ℝ} {c : (K).X n} (hc : c ∈ affineMeshSubmodule R s n D) :
    (End.of (singularSubdivision R (TopCat.of E)) ^ m).f n c ∈
      affineMeshSubmodule R s n (((n : ℝ) / (n + 1)) ^ m * D) := by
  induction m with
  | zero => simpa only [pow_zero, End.one_def, HomologicalComplex.id_f,
      ModuleCat.id_apply, one_mul] using hc
  | succ m hm =>
    rw [pow_succ' (End.of (singularSubdivision R (TopCat.of E))) m, End.mul_def, HomologicalComplex.comp_f, ModuleCat.comp_apply]
    have h := affineMeshSubmodule_le_comap_subdivision R hs n
      (((n : ℝ) / (n + 1)) ^ m * D) hm
    simpa only [Submodule.mem_comap, pow_succ', mul_assoc, singularSubdivision_f] using h


theorem exists_uniform_subdivision_mesh_threshold {s : Set E} (hs : Convex ℝ s)
    (n : ℕ) (D : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ m ≥ N,
      ((n : ℝ) / (n + 1)) ^ m * D < ε ∧
      ∀ c ∈ affineMeshSubmodule R s n D,
        (End.of (singularSubdivision R (TopCat.of E)) ^ m).f n c ∈
          affineMeshSubmodule R s n (((n : ℝ) / (n + 1)) ^ m * D) := by
  have hr0 : (0 : ℝ) ≤ (n : ℝ) / (n + 1) := by positivity
  have hr1 : (n : ℝ) / (n + 1) < 1 :=
    (div_lt_one (by positivity)).mpr (lt_add_one (n : ℝ))
  have ht : Filter.Tendsto (fun m : ℕ ↦ ((n : ℝ) / (n + 1)) ^ m * D)
      Filter.atTop (nhds 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const D
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ((tendsto_order.mp ht).2 ε hε)
  exact ⟨N, fun m hm ↦ ⟨hN m hm,
    fun _ hc ↦ singularSubdivision_pow_mem_affineMeshSubmodule R hs n m hc⟩⟩

end DifferentialGeometry.Homology
