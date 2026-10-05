module

public import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Stabilizer slices for properly discontinuous actions

A properly discontinuous action on a locally compact Hausdorff space admits an open slice at
every point. The slice is invariant under the point stabilizer, and no other translate meets it.
-/

@[expose] public section

open Set Topology

namespace SphereSixComplex.Geometry

universe u v

variable {G : Type u} {X : Type v} [Group G] [TopologicalSpace X] [MulAction G X]
  [ProperlyDiscontinuousSMul G X] [T2Space X] [LocallyCompactSpace X]
  [ContinuousConstSMul G X]

/-- A properly discontinuous action has an open stabilizer-invariant slice at every point.
Precisely the elements in the point stabilizer have a translate meeting the slice. -/
public theorem exists_open_stabilizer_slice (x : X) :
    ∃ U : Set X,
      IsOpen U ∧
      x ∈ U ∧
      (∀ h : MulAction.stabilizer G x, (fun y : X ↦ (h : G) • y) '' U = U) ∧
      ∀ g : G, ((fun y : X ↦ g • y) '' U ∩ U).Nonempty ↔
        g ∈ MulAction.stabilizer G x := by
  obtain ⟨W, hWnhds, hW⟩ :=
    ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self G x
  obtain ⟨V, hVW, hVopen, hxV⟩ := mem_nhds_iff.mp hWnhds
  let H := MulAction.stabilizer G x
  let _ : Finite H := Set.finite_coe_iff.mpr
    (ProperlyDiscontinuousSMul.finite_stabilizer x)
  let U := ⋂ h : H, (fun y : X ↦ (h : G) • y) ⁻¹' V
  have hUopen : IsOpen U := by
    apply isOpen_iInter_of_finite
    intro h
    exact hVopen.preimage (continuous_const_smul (h : G))
  have hxU : x ∈ U := by
    simp only [U, Set.mem_iInter]
    intro h
    change (h : G) • x ∈ V
    rw [h.property]
    exact hxV
  have hUV : U ⊆ V := by
    intro y hy
    have hy' : ∀ h : H, (h : G) • y ∈ V := by
      simpa only [U, Set.mem_iInter, Set.mem_preimage] using hy
    simpa using hy' 1
  have hUW : U ⊆ W := hUV.trans hVW
  have hInvariant : ∀ h : H, (fun y : X ↦ (h : G) • y) '' U = U := by
    intro h
    apply Set.Subset.antisymm
    · rintro z ⟨y, hy, rfl⟩
      have hy' : ∀ k : H, (k : G) • y ∈ V := by
        simpa only [U, Set.mem_iInter, Set.mem_preimage] using hy
      simp only [U, Set.mem_iInter, Set.mem_preimage]
      intro k
      have hkh := hy' (k * h)
      simpa [mul_smul] using hkh
    · intro z hz
      refine ⟨(h : G)⁻¹ • z, ?_, by simp⟩
      have hz' : ∀ k : H, (k : G) • z ∈ V := by
        simpa only [U, Set.mem_iInter, Set.mem_preimage] using hz
      simp only [U, Set.mem_iInter, Set.mem_preimage]
      intro k
      have hkh := hz' (k * h⁻¹)
      simpa [mul_smul] using hkh
  refine ⟨U, hUopen, hxU, hInvariant, fun g ↦ ⟨?_, ?_⟩⟩
  · intro hg
    show g • x = x
    apply hW g
    obtain ⟨z, ⟨y, hy, rfl⟩, hz⟩ := hg
    exact ⟨g • y, ⟨y, hUW hy, rfl⟩, hUW hz⟩
  · intro hg
    rw [hInvariant ⟨g, hg⟩]
    exact ⟨x, hxU, hxU⟩

end SphereSixComplex.Geometry
