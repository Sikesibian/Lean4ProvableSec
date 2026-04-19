import ProvableSec.Defination.CryptoNotation
import ProvableSec.ClassicTheorem.YaoTheorem

/-!
# CryptoNotation Usage Examples

中文：展示如何使用全局概率语义接口，以及如何在 Yao 层调用 OWF 叙述。
English: show usage of global probability semantics and Yao-layer OWF statements.
-/

namespace ProvableSec.Examples

open ProvableSec.CryptoNotation
open scoped CryptoNotation

section GlobalSemanticsUsage

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

end GlobalSemanticsUsage

section OWFProbabilityNotationUsage

variable (C : Context)
variable (M : Context.OWF.Model C)
variable (f : Context.OWF.OWFunction)
variable (A : Context.OWF.Adversary C)
variable (n : Nat)

example :
    PrFail[M|f](A, n) = 1 - Pr[M|f](A, n) := by
  simpa using M.PrFail_eq f A n

example :
    0 ≤ Pr[M|f](A, n) := by
  simpa using M.Pr_nonneg f A n

example :
    Pr[M|f](A, n) ≤ 1 := by
  simpa using M.Pr_le_one f A n

end OWFProbabilityNotationUsage

section YaoUsage

variable (C : Context)
variable (M : Context.Yao.Model C)
variable (R : Context.Yao.ReductionSpec C M)
variable (hRed : Context.Yao.ReductionCorrect C M R)
variable (T : Context.Yao.Family → Context.Yao.Family)
variable (hT :
  ∀ F : Context.Yao.Family,
    Context.Yao.WeakOWF C M F → Context.Yao.StrongOWF C M (T F))
variable (H : Context.Yao.TextbookYaoHypothesis C M)
variable (f : Context.Yao.Family)

example :
    Context.Yao.weak_to_strong_transform C M := by
  exact ⟨T, hT⟩

example :
    Context.Yao.weak_to_strong_existential C M := by
  exact Context.Yao.transform_implies_existential C M ⟨T, hT⟩

example :
    Context.Yao.WeakOWF C M f →
      Context.Yao.StrongOWF C M (H.lift f) := by
  exact Context.Yao.textbook_yao_of_hyp C M H f

example :
    Context.Yao.LiftSound C M R := by
  exact Context.Yao.reductionCorrect_implies_liftSound C M R hRed

example :
    Context.Yao.weak_to_strong_transform C M := by
  exact Context.Yao.reductionCorrect_implies_transform C M R hRed

example :
    Context.Yao.weak_to_strong_existential C M := by
  exact Context.Yao.reductionCorrect_implies_existential C M R hRed

end YaoUsage

end ProvableSec.Examples
