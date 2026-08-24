module

public import SphereSixComplex.Geometry.EllipticFamilySpecialization

/-!
# The topological group structure of an actual period torus

The period torus was introduced as an orbit quotient because that presentation is used by the
family actions.  This module identifies it with the standard quotient additive group and transports
the continuity of addition and negation back to the orbit presentation.
-/

namespace SphereSixComplex.Geometry.AdditiveTorusTopology

open SphereSixComplex.Periods
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization

noncomputable section

/-- Translation-orbit equivalence is exactly congruence modulo the period lattice. -/
public theorem orbitRel_iff_sub_mem (x : Parameters) (z w : ComplexTwoSpace) :
    MulAction.orbitRel (PeriodGroup x) ComplexTwoSpace z w ↔
      z - w ∈ periodLattice x := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩
    change (g.toAdd : ComplexTwoSpace) + w = z at hg
    rw [← hg]
    simpa only [add_sub_cancel_right] using g.toAdd.2
  · intro h
    let g : PeriodGroup x := Multiplicative.ofAdd ⟨z - w, h⟩
    refine ⟨g, ?_⟩
    change (z - w) + w = z
    abel

public theorem orbitRel_to_leftRel (x : Parameters) (z w : ComplexTwoSpace)
    (h : MulAction.orbitRel (PeriodGroup x) ComplexTwoSpace z w) :
    (QuotientAddGroup.leftRel (periodLattice x)) z w := by
  rw [QuotientAddGroup.leftRel_apply]
  rw [show -z + w = -(z - w) by abel]
  exact (periodLattice x).neg_mem ((orbitRel_iff_sub_mem x z w).mp h)

public theorem leftRel_to_orbitRel (x : Parameters) (z w : ComplexTwoSpace)
    (h : (QuotientAddGroup.leftRel (periodLattice x)) z w) :
    MulAction.orbitRel (PeriodGroup x) ComplexTwoSpace z w := by
  apply (orbitRel_iff_sub_mem x z w).mpr
  rw [QuotientAddGroup.leftRel_apply] at h
  have hn := (periodLattice x).neg_mem h
  rwa [show -(-z + w) = z - w by abel] at hn

/-- The orbit presentation mapped to the standard quotient additive group. -/
@[expose] public def toAddQuotient (x : Parameters) :
    AdditiveTorus x → ComplexTwoSpace ⧸ periodLattice x :=
  Quotient.map id (orbitRel_to_leftRel x)

/-- The standard quotient additive group mapped back to the orbit presentation. -/
@[expose] public def ofAddQuotient (x : Parameters) :
    (ComplexTwoSpace ⧸ periodLattice x) → AdditiveTorus x :=
  Quotient.map id (leftRel_to_orbitRel x)

@[simp]
public theorem toAddQuotient_mk (x : Parameters) (z : ComplexTwoSpace) :
    toAddQuotient x (Quotient.mk _ z) = QuotientAddGroup.mk z :=
  rfl

@[simp]
public theorem ofAddQuotient_mk (x : Parameters) (z : ComplexTwoSpace) :
    ofAddQuotient x (QuotientAddGroup.mk z) = Quotient.mk _ z :=
  rfl

/-- The two quotient presentations are canonically homeomorphic. -/
@[expose] public def homeomorphAddQuotient (x : Parameters) :
    AdditiveTorus x ≃ₜ ComplexTwoSpace ⧸ periodLattice x where
  toFun := toAddQuotient x
  invFun := ofAddQuotient x
  left_inv q := by
    induction q using Quotient.inductionOn with
    | _ z => rfl
  right_inv q := by
    induction q using Quotient.inductionOn with
    | _ z => rfl
  continuous_toFun := continuous_quot_map (orbitRel_to_leftRel x) continuous_id
  continuous_invFun := continuous_quot_map (leftRel_to_orbitRel x) continuous_id

@[simp]
public theorem toAddQuotient_add (x : Parameters) (q r : AdditiveTorus x) :
    toAddQuotient x (q + r) = toAddQuotient x q + toAddQuotient x r := by
  induction q using Quotient.inductionOn with
  | _ z =>
      induction r using Quotient.inductionOn with
      | _ w => rfl

@[simp]
public theorem toAddQuotient_neg (x : Parameters) (q : AdditiveTorus x) :
    toAddQuotient x (-q) = -toAddQuotient x q := by
  induction q using Quotient.inductionOn with
  | _ z => rfl

public noncomputable instance (x : Parameters) : ContinuousAdd (AdditiveTorus x) where
  continuous_add := by
    let h := homeomorphAddQuotient x
    have hc : Continuous (fun p : AdditiveTorus x × AdditiveTorus x ↦
        h.symm (h p.1 + h p.2)) :=
      h.symm.continuous.comp
        ((h.continuous.comp continuous_fst).add (h.continuous.comp continuous_snd))
    convert hc using 1
    funext p
    symm
    change h.symm (toAddQuotient x p.1 + toAddQuotient x p.2) = p.1 + p.2
    rw [← toAddQuotient_add]
    exact h.symm_apply_apply _

public noncomputable instance (x : Parameters) : ContinuousNeg (AdditiveTorus x) where
  continuous_neg := by
    let h := homeomorphAddQuotient x
    have hc : Continuous (fun q : AdditiveTorus x ↦ h.symm (-h q)) :=
      h.symm.continuous.comp h.continuous.neg
    convert hc using 1
    funext q
    symm
    change h.symm (-toAddQuotient x q) = -q
    rw [← toAddQuotient_neg]
    exact h.symm_apply_apply _

public noncomputable instance (x : Parameters) : IsTopologicalAddGroup (AdditiveTorus x) :=
  ⟨⟩

/-- The orbit presentation inherits second countability from the standard quotient additive
group. -/
public noncomputable instance (x : Parameters) :
    SecondCountableTopology (AdditiveTorus x) :=
  (homeomorphAddQuotient x).secondCountableTopology

end


end SphereSixComplex.Geometry.AdditiveTorusTopology
