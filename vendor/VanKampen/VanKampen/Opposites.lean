module

public import Mathlib.CategoryTheory.Limits.Preserves.Opposites

/-!
# Preservation of opposite limits and colimits

Compatibility instances from Paul-Lez/mathlib4 at 97d303eb50436be7c4bac4388bdb49459ae9140b.
-/

@[expose] public section

namespace CategoryTheory.Limits

universe u₁ u₂ u₃ v₁ v₂ v₃

variable {J : Type u₁} [Category.{v₁} J]
variable {C : Type u₂} [Category.{v₂} C] {D : Type u₃} [Category.{v₃} D]

/-- If `F : C ⥤ D` preserves colimits of `K : J ⥤ C`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves
limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`. -/
instance PreservesColimit.op (K : J ⥤ C) (F : C ⥤ D) [PreservesColimit K F] :
    PreservesLimit K.op F.op where
  preserves {_} hc := ⟨(isColimitOfPreserves F hc.unop).op⟩

/-- If `F : C ⥤ D` preserves limits of `K : J ⥤ C`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves
colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`. -/
instance PreservesLimit.op (K : J ⥤ C) (F : C ⥤ D) [PreservesLimit K F] :
    PreservesColimit K.op F.op where
  preserves {_} hc := ⟨(isLimitOfPreserves F hc.unop).op⟩

end CategoryTheory.Limits
