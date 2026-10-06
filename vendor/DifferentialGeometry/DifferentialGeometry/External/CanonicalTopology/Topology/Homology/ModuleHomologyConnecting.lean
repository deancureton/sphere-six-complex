module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ModuleHomologyClasses
public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace DifferentialGeometry.Topology

variable {R : Type u} [Ring R]

private theorem moduleCycleIso_inv_eq_cyclesMk
    (S : ShortComplex (ModuleCat.{v} R)) (c : LinearMap.ker S.g.hom) :
    S.moduleCatCyclesIso.inv c = S.cyclesMk c.val c.property := by
  apply (ModuleCat.mono_iff_injective S.iCycles).mp inferInstance
  have h := congrArg (fun f : S.moduleCatLeftHomologyData.K ⟶ S.X₂ => f c)
    S.moduleCatCyclesIso_inv_iCycles
  change S.iCycles (S.moduleCatCyclesIso.inv c) = c.val at h
  exact h.trans (S.i_cyclesMk c.val c.property).symm

theorem moduleHomologyClass_connecting
    {ι : Type*} {shape : ComplexShape ι}
    {S : ShortComplex (HomologicalComplex (ModuleCat.{v} R) shape)} (hS : S.ShortExact)
    (i j : ι) (hij : shape.Rel i j) (c : LinearMap.ker (S.X₃.sc i).g.hom)
    (b : S.X₂.X i) (hb : S.g.f i b = c.val)
    (a : LinearMap.ker (S.X₁.sc j).g.hom) (ha : S.f.f j a.val = S.X₂.d i j b) :
    hS.δ i j hij (moduleHomologyClass (S.X₃.sc i) c) =
      moduleHomologyClass (S.X₁.sc j) a := by
  have hc : S.X₃.d i j c.val = 0 := by
    have h := c.property
    change S.X₃.d i (shape.next i) c.val = 0 at h
    rwa [shape.next_eq' hij] at h
  have h := hS.δ_apply i j hij c.val hc b hb a.val ha (shape.next j) rfl
  have h3 : (S.X₃.cyclesMk c.val j (shape.next_eq' hij) hc) =
      (S.X₃.sc i).moduleCatCyclesIso.inv c := by
    exact (moduleCycleIso_inv_eq_cyclesMk (S.X₃.sc i) c).symm
  have h1 : (S.X₁.cyclesMk a.val (shape.next j) rfl
      (hS.d_eq_zero_of_f_eq_d_apply i j b a.val ha _)) =
      (S.X₁.sc j).moduleCatCyclesIso.inv a := by
    exact (moduleCycleIso_inv_eq_cyclesMk (S.X₁.sc j) a).symm
  rw [h3, h1] at h
  exact h

theorem exists_moduleCycle_connecting_lifts
    {R : Type u} [Ring R] {ι : Type*} {shape : ComplexShape ι}
    {S : ShortComplex (HomologicalComplex (ModuleCat.{v} R) shape)} (hS : S.ShortExact)
    (i j : ι) (hij : shape.Rel i j) (c : LinearMap.ker (S.X₃.sc i).g.hom) :
    ∃ b : S.X₂.X i, ∃ a : LinearMap.ker (S.X₁.sc j).g.hom,
      S.g.f i b = c.val ∧ S.f.f j a.val = S.X₂.d i j b := by
  have hi := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS i
  have hj := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS j
  obtain ⟨b, hb⟩ := (ModuleCat.epi_iff_surjective (S.g.f i)).mp hi.epi_g c.val
  have hc : S.X₃.d i j c.val = 0 := by
    have h := c.property
    change S.X₃.d i (shape.next i) c.val = 0 at h
    rwa [shape.next_eq' hij] at h
  have hdb : S.g.f j (S.X₂.d i j b) = 0 := by
    have h := congrArg (fun f : S.X₂.X i ⟶ S.X₃.X j => f b) (S.g.comm i j)
    change S.X₃.d i j (S.g.f i b) = S.g.f j (S.X₂.d i j b) at h
    rw [hb, hc] at h
    exact h.symm
  obtain ⟨a, ha⟩ := (ShortComplex.moduleCat_exact_iff _).mp hj.exact _ hdb
  have haCycle : a ∈ LinearMap.ker (S.X₁.sc j).g.hom :=
    hS.d_eq_zero_of_f_eq_d_apply i j b a ha (shape.next j)
  exact ⟨b, ⟨a, haCycle⟩, hb, ha⟩


end DifferentialGeometry.Topology

end
