/-
Copyright (c) 2025 Michael P. Lane. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael P. Lane
-/

import Mathlib.Analysis.Convex.Basic

/-!
# Geometric properties of fixed points
-/

namespace AffineMap

theorem convex_fixedPoints
{V R : Type*} [AddCommGroup V] [Ring R] [Module R V] [PartialOrder R] [IsOrderedRing R]
(T : V →ᵃ[R] V)
: Convex R (Function.fixedPoints T) := by
  intro _ mem_fixedPoints1 _ mem_fixedPoints2; intros
  rwa [Function.mem_fixedPoints_iff, Convex.combo_affine_apply,
    Function.mem_fixedPoints_iff.mp mem_fixedPoints1,
    Function.mem_fixedPoints_iff.mp mem_fixedPoints2]

end AffineMap
