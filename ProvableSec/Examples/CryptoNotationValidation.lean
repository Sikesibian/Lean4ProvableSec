import ProvableSec.Defination.CryptoNotation
import ProvableSec.ClassicTheorem.YaoTheorem

/-!
# CryptoNotation Validation Examples

中文：验证全局概率语义接口的基本性质，并验证 Yao 层接口可用。
English: validate basic properties of global semantics and Yao-layer interfaces.
-/

namespace ProvableSec.Examples

open ProvableSec.CryptoNotation
open scoped CryptoNotation

section GlobalSemanticsValidation

variable (C : Context)
variable (M : Context.Model C)
variable (A : Context.Adversary C)
variable (n : Nat)

example :
    PrFail[M](A, n) = 1 - Pr[M](A, n) := by
  simpa using M.PrFail_eq A n

example :
    0 ≤ Pr[M](A, n) := by
  simpa using M.Pr_nonneg A n

example :
    Pr[M](A, n) ≤ 1 := by
  simpa using M.Pr_le_one A n

end GlobalSemanticsValidation

section YaoValidation

variable (C : Context)
variable (M : Context.Yao.Model C)
variable (R : Context.Yao.ReductionSpec C M)
variable (hRed : Context.Yao.ReductionCorrect C M R)
variable (P : Context.Yao.ProofPlan C M)

example :
    Context.Yao.weak_to_strong_transform C M →
      Context.Yao.weak_to_strong_existential C M := by
  intro h
  exact Context.Yao.transform_implies_existential C M h

example :
    Context.Yao.weak_to_strong_same_family C M →
      Context.Yao.weak_to_strong_transform C M := by
  intro h
  exact Context.Yao.same_family_implies_transform C M h

example :
    Context.Yao.ReductionCorrect C M R →
      Context.Yao.weak_to_strong_transform C M := by
  intro h
  exact Context.Yao.reductionCorrect_implies_transform C M R h

example :
    Context.Yao.weak_to_strong_transform C M := by
  exact Context.Yao.plan_implies_transform C M P

example :
    Context.Yao.weak_to_strong_existential C M := by
  exact Context.Yao.plan_implies_existential C M P

end YaoValidation

end ProvableSec.Examples
