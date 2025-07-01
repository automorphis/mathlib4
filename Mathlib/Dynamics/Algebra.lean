/-
Copyright (c) 2025 Michael P. Lane. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael P. Lane
-/

import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Data.FunLike.Basic
import Mathlib.Logic.Function.Conjugate

/-!
# Monoids of functions with composition.

This module is an interface between the algebraic and set-theoretic properties of composing
self-maps. The basic type class of this module is `CompSemigroup`. A type `F` can instance
`CompSemigroup` whenever `F` consists of bundled functions and composing elements of `F` agrees with
composing the unbundled functions. For example, the type `F := V →ₗ[R] V` of `R`-linear
endomorphisms of a vector space `V` can instance `CompSemigroup` because `LinearMap.comp` merely
composes the unbundled linear maps.

## Main definitions:

* `CompSemigroup`
* `CompMonoid`
* `CompGroup`
-/

section Defs

variable (F : Type*) (X : outParam Type*) [FunLike F X X]

class CompSemigroup where
  comp : F → F → F
  coe_hom : ∀ f g : F, ⇑(comp f g) = ⇑f ∘ ⇑g

class CompMonoid extends CompSemigroup F X where
  id' : F
  coe_id : ⇑id' = id

class CompGroup [Nonempty X] extends CompMonoid F X where
  inv : F → F
  coe_injective : ∀ f : F, Function.Injective f
  coe_inv : ∀ f : F, ⇑(inv f) = (⇑f).invFun

end Defs

section

variable {F X : Type*} [FunLike F X X]

namespace CompSemigroup

variable [CompSemigroup F X]

theorem comp_assoc (f g h : F)
: comp (comp f g) h = comp f (comp g h) := by
  apply DFunLike.coe_injective'
  repeat rw[coe_hom]
  rfl

instance : Semigroup F where
  mul := CompSemigroup.comp
  mul_assoc := CompSemigroup.comp_assoc

theorem mul_def
: ∀ f g : F, f * g = CompSemigroup.comp f g :=
  fun _ _ ↦ rfl

theorem function_commute_iff_commute (f g : F)
: Function.Commute f g ↔ Commute f g := by
  constructor <;> intro comm
  · apply DFunLike.coe_injective'
    repeat rw[mul_def, coe_hom]
    exact comm.comp_eq
  · refine congrFun (?_ : f ∘ g = g ∘ f)
    repeat rw [←coe_hom]
    exact congrArg DFunLike.coe comm

theorem forall_function_commute_iff_isMulCommutative
: (∀ f g : F, Function.Commute f g) ↔ IsMulCommutative F := by
  constructor
  · exact fun comm ↦ ⟨⟨fun f g ↦ (function_commute_iff_commute f g).mp <| comm f g⟩⟩
  · exact fun inst f g ↦ (function_commute_iff_commute f g).mpr <| inst.is_comm.comm f g

end CompSemigroup

namespace CompMonoid

variable [CompMonoid F X]

theorem comp_id
: ∀ f : F, CompSemigroup.comp f id' = f := by
  intros
  apply DFunLike.coe_injective'
  rw[CompSemigroup.coe_hom, coe_id]
  rfl

theorem id_comp
: ∀ f : F, CompSemigroup.comp id' f = f := by
  intros
  apply DFunLike.coe_injective'
  rw[CompSemigroup.coe_hom, coe_id]
  rfl

instance : Monoid F where
  one := CompMonoid.id'
  mul_one := CompMonoid.comp_id
  one_mul := CompMonoid.id_comp

end CompMonoid

namespace CompGroup

variable [Nonempty X] [CompGroup F X]

theorem inv_comp_cancel
: ∀ f : F, CompSemigroup.comp (inv f) f = CompMonoid.id' := by
  intros
  apply DFunLike.coe_injective'
  rw[CompSemigroup.coe_hom, coe_inv, CompMonoid.coe_id]
  exact Function.invFun_comp <| coe_injective _

instance : Group F where
  inv := CompGroup.inv
  inv_mul_cancel := CompGroup.inv_comp_cancel

end CompGroup

end
