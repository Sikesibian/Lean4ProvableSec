import ProvableSec.Defination.CryptoNotation
import ProvableSec.ClassicTheorem.YaoTheorem

/-!
# CryptoNotation Concrete Example

中文：
给出最小具体对象示例：
- 全局语义（随机带诱导概率）
- Yao 层 OWF 模型（用于 weak/strong 叙述）

English:
Minimal concrete examples for:
- global random-tape semantics
- Yao-layer OWF model
-/

namespace ProvableSec.Examples

open ProvableSec.CryptoNotation
open scoped CryptoNotation

namespace Concrete

abbrev K0 : Type := Unit
abbrev L0 : Type := Unit
abbrev S0 : Type := Unit

/-- 将具体机器参数一次性打包。 -/
def C0 : Context :=
  { K := K0
    Λ := L0
    σ := S0
    decEqK := inferInstance
    inhΛ := inferInstance
    inhσ := inferInstance }

abbrev GlobalModel0 : Type := Context.Model C0
abbrev Adv0 : Type := Context.Adversary C0

/-- 线性函数 `n ↦ n` 满足简化多项式有界。 -/
theorem linear_isPolynomial : TuringMachine.Crypto.IsPolynomial (fun n : Nat => n) := by
  refine ⟨1, 1, ?_⟩
  intro n
  calc
    n ≤ n + 1 := Nat.le_succ n
    _ = 1 * (n + 1) ^ 1 := by simp

/-- 全局语义示例：成功概率恒为 0。 -/
def toyGlobalModel : GlobalModel0 where
  successProb := fun _ _ => 0
  successProb_range := by
    intro A n
    constructor <;> simp

section GlobalChecks

variable (A : Adv0)
variable (n : Nat)

example :
    Pr[toyGlobalModel](A, n) = 0 :=
  rfl

example :
    PrFail[toyGlobalModel](A, n) = 1 := by
  simp [Context.Model.PrFail, Context.PrFail,
    CryptoNotation.PrFail, CryptoNotation.Pr, toyGlobalModel]

example :
    PrFail[toyGlobalModel](A, n) = 1 - Pr[toyGlobalModel](A, n) := by
  simpa using toyGlobalModel.PrFail_eq A n

end GlobalChecks

end Concrete
end ProvableSec.Examples
