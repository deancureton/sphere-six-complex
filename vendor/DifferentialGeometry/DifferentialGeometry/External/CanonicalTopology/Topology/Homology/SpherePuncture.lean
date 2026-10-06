module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RadialHomotopy
public import Mathlib.Geometry.Manifold.Instances.Sphere

@[expose] public section

/-! # The actual punctured sphere and stereographic coordinates -/

noncomputable section

open ContinuousMap Set Metric
open scoped Topology

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E]

section

variable [NormedSpace ℝ E]

/-- A unit vector and its antipode are distinct. -/
theorem unitSphere_ne_antipode (v : sphere (0 : E) 1) : v ≠ -v := by
  intro h
  have he : (v : E) = -(v : E) := congrArg Subtype.val h
  have hz : (2 : ℝ) • (v : E) = 0 := by
    rw [two_smul]
    exact (congrArg (fun x : E => x + (v : E)) he).trans (neg_add_cancel _)
  have hv : (v : E) = 0 := (smul_eq_zero.mp hz).resolve_left (by norm_num)
  have hn := norm_eq_of_mem_sphere v
  rw [hv, norm_zero] at hn
  norm_num at hn

end

variable [InnerProductSpace ℝ E]

/-- Stereographic projection identifies the original sphere minus its
specified pole with the actual orthogonal hyperplane. -/
def spherePunctureHomeomorph (v : sphere (0 : E) 1) :
    ({v}ᶜ : Set (sphere (0 : E) 1)) ≃ₜ (ℝ ∙ (v : E))ᗮ :=
  (stereographic (norm_eq_of_mem_sphere v)).toHomeomorphSourceTarget.trans
    (Homeomorph.Set.univ _)

/-- This homeomorphism uses the original stereographic map. -/
theorem spherePunctureHomeomorph_apply (v : sphere (0 : E) 1)
    (x : ({v}ᶜ : Set (sphere (0 : E) 1))) :
    spherePunctureHomeomorph v x = stereographic (norm_eq_of_mem_sphere v) x.val := rfl

/-- Every actual single-pole complement is contractible. -/
theorem spherePuncture_contractible (v : sphere (0 : E) 1) :
    ContractibleSpace ({v}ᶜ : Set (sphere (0 : E) 1)) :=
  (spherePunctureHomeomorph v).contractibleSpace


/-- The two original antipodal pole complements cover the entire sphere. -/
theorem spherePunctures_cover (v : sphere (0 : E) 1) :
    ({v}ᶜ : Set (sphere (0 : E) 1)) ∪ {-v}ᶜ = univ := by
  ext x
  simp only [mem_union, mem_compl_iff, mem_singleton_iff, mem_univ, iff_true]
  by_cases h : x = v
  · exact Or.inr (h ▸ unitSphere_ne_antipode v)
  · exact Or.inl h

/-- Within the opposite-pole chart, the omitted north pole is exactly
coordinate zero, so the same two-pole intersection is a punctured hyperplane. -/
def sphereDoublePunctureHomeomorph (v : sphere (0 : E) 1) :
    {x : ({-v}ᶜ : Set (sphere (0 : E) 1)) | x.val ≠ v} ≃ₜ
      ({0}ᶜ : Set (ℝ ∙ ((-v : sphere (0 : E) 1) : E))ᗮ) := by
  let p : ({-v}ᶜ : Set (sphere (0 : E) 1)) := ⟨v, unitSphere_ne_antipode v⟩
  have hp : spherePunctureHomeomorph (-v) p = 0 := stereographic_neg_apply v
  refine (spherePunctureHomeomorph (-v)).subtype (fun x => ?_)
  change (x.val ≠ v) ↔ spherePunctureHomeomorph (-v) x ≠ 0
  rw [← hp, (spherePunctureHomeomorph (-v)).injective.ne_iff]
  apply not_congr
  constructor
  · intro h
    exact Subtype.ext h
  · intro h
    exact congrArg Subtype.val h

end DifferentialGeometry.Topology
