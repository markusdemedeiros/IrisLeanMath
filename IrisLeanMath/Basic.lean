import Mathlib.Probability.Independence.Basic
import Iris

noncomputable section

open Iris ProbabilityTheory MeasureTheory

variable {Ω : Type _} [MeasurableSpace Ω]

/-- Real-valued random variable -/
@[ext] structure RandomVariable (δ : Type _) (μ : Measure Ω) where
  car : Ω → δ

-- instance : FunLike (RandomVariable Ω δ) Ω δ where
--   coe := (·.car)
--   coe_injective' _ _ H := RandomVariable.ext H

-- instance : Coe (RandomVariable Ω δ) (Ω → δ) := ⟨(·.car)⟩
-- instance : Coe (Ω → δ) (RandomVariable Ω δ) := ⟨.mk⟩

namespace RealRandomVariableMax

/-- OFE for ae equality of the random variables -/
scoped instance aeOFE {μ : Measure Ω} : OFE (RandomVariable ℝ μ) where
  Equiv x y := x.car =ᵐ[μ] y.car
  Dist _ x y := x.car =ᵐ[μ] y.car
  dist_eqv {_} := {
    refl _ := ae_eq_rfl
    symm := (Filter.EventuallyEq.symm ·)
    trans := (ae_eq_trans · ·)
  }
  equiv_dist := .symm <| forall_const _
  dist_lt H _ := H

/-- Basic: CMRA of random variables in a fixed measure μ which combines by max. -/
scoped instance maxCMRA {μ : Measure Ω} : CMRA (RandomVariable ℝ μ) where
  pcore := .some
  op r₁ r₂ := ⟨fun s ↦ max (r₁.car s) (r₂.car s)⟩
  ValidN _ _ := True
  Valid _ := True
  op_ne {x} := .mk (fun _ _ _ H => Filter.eventuallyEq_of_mem H (congrArg <| max <| x.car ·))
  pcore_ne {n x y cx} := by
    rintro H ⟨rfl⟩
    exact ⟨y, rfl, H⟩
  validN_ne _ _ := trivial
  valid_iff_validN := .symm (imp_true_iff _)
  validN_succ _ := trivial
  validN_op_left _ := trivial
  assoc := .of_eq <| RandomVariable.ext <| funext fun _ => (max_assoc ..).symm
  comm := .of_eq <| RandomVariable.ext <| funext fun _ => (max_comm ..)
  pcore_op_left {_ _} := by
    rintro ⟨rfl⟩
    exact .of_eq <| RandomVariable.ext <| funext fun _ => (max_self ..)
  pcore_idem _ := .rfl
  pcore_op_mono {_ _} := by
    rintro ⟨rfl⟩ y; refine ⟨y, .rfl⟩
  extend {_ _ y₁ y₂} _ H := ⟨y₁, y₂, H.trans <| .of_eq rfl, .rfl, .rfl⟩

end RealRandomVariableMax


--  generalize the codomain of the RV to another CMRA? What needs to be measurable


-- op for indendependent sets
