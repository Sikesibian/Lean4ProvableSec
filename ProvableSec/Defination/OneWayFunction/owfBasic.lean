import ProvableSec.Defination.Baisc.Complexity.ComplexityClass
import ProvableSec.Defination.Baisc.TuringMachine.TMCrypto
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

/-!
# One-Way Function Basic Definitions

## 目标 / Goals
- 中文：基于已有 TM/PPT/复杂度接口，给出 weak OWF 与 strong OWF 的专业定义。
- English: provide professional definitions of weak and strong OWFs on top of existing TM/PPT/complexity interfaces.

## 核心思想 / Core Idea
- 中文：将“反演成功概率”抽象为接口 `OWFSemantics`，从而把概率层与机器语义层解耦。
- English: abstract inversion success probability via `OWFSemantics`, decoupling probability semantics from machine semantics.

## 公式 / Formulas

可忽略函数接口：

$$
\forall c\in\mathbb{N},\ \exists n_0,\ \forall n\ge n_0,
\ |\varepsilon(n)| \le \frac{1}{(n+1)^c}.
$$

weak OWF：

$$
\forall A\in PPT,\ \exists p\in Poly^+,\ \exists n_0,\ \forall n\ge n_0,
\ \Pr[A(f_n(U_n))\in f_n^{-1}(f_n(U_n))] \le 1 - \frac{1}{p(n)}.
$$

strong OWF：

$$
\forall A\in PPT,\ \Pr[A(f_n(U_n))\in f_n^{-1}(f_n(U_n))]
\text{ is negligible in } n.
$$
-/

namespace OneWayFunction

open Complexity
open TuringMachine.Crypto

/-- 比特串别名。 -/
abbrev Bits : Type := Complexity.Bits

/-- 正值多项式函数（`Nat → Nat`）。 -/
def IsPosPoly (p : Nat → Nat) : Prop :=
  IsPolynomial p ∧ ∀ n, 0 < p n

/-- 可忽略函数（`Nat → ℝ`）。 -/
def IsNegligible (ε : Nat → ℝ) : Prop :=
  ∀ c : Nat, ∃ n0 : Nat, ∀ n : Nat, n ≥ n0 →
    |ε n| ≤ (1 : ℝ) / (((n + 1 : Nat) : ℝ) ^ c)

/--
可高效计算的函数族接口（参数化按安全参数 `n`）。
`eval n x` 表示安全参数为 `n` 时函数值。
-/
structure EfficientFamily where
  eval : Nat → Bits → Bits
  timeBound : Nat → Nat
  timeBound_poly : IsPolynomial timeBound
  outLenBound : Nat → Nat
  outLenBound_poly : IsPolynomial outLenBound
  outLen_spec : ∀ n x, x.length = n → (eval n x).length ≤ outLenBound n

/--
OWF 常用函数族约束：在上面效率接口基础上加长度保持。
-/
structure OWFFamily extends EfficientFamily where
  lengthPreserving : ∀ n x, x.length = n → (eval n x).length = n

section SecurityGames

/--
**求逆实验 (Inversion Game) 概率的显式计算核心**

`inversionSuccessProb F A n` 计算：
在安全参数 `n` 下，PPT 敌手 `A` 对 `F` 成功求逆的概率。
由于 $x$ 是均匀采样的，我们遍历所有长度为 $n$ 的比特串，
并调用底层的 `probEvent` (已在内部遍历均匀随机币) 来计算期望成功率。
-/
noncomputable def inversionSuccessProb (F : OWFFamily) (A : BitPPTAdversary) (n : Nat) : ℝ :=
  by
  classical
  exact
    let inputs := allCoins n
    let totalInputs := inputs.card
    if totalInputs = 0 then 0 else
      -- 遍历所有均匀选择的 x
      let sumProbs : ℝ := inputs.sum (fun x =>
        let y := F.eval n x
        -- 对于特定的 x 及其对应的 y，敌手 A 能输出合法原像的概率
        -- 注意：由于 P 必须是 DecidablePred，List Bool 的相等性天然满足。
        BitPPTAdversary.probEvent A y (fun out => F.eval n out = y)
      )
      sumProbs / (totalInputs : ℝ)

/-- 失败概率接口。 -/
noncomputable def failureProb (F : OWFFamily) (A : BitPPTAdversary) (n : Nat) : ℝ :=
  1 - inversionSuccessProb F A n

/--
**weak OWF 定义：**
任意 PPT 反演器都不能以“趋近 1 的概率”成功，
至少有 `1/p(n)` 级别的失败间隙。
-/
def IsWeakOWF (F : OWFFamily) : Prop :=
  ∀ A : BitPPTAdversary,
    ∃ p : Nat → Nat,
      IsPosPoly p ∧
      ∃ n0 : Nat,
        ∀ n : Nat, n ≥ n0 →
          inversionSuccessProb F A n ≤ 1 - (1 : ℝ) / (p n : ℝ)

/--
**δ-weak OWF 定义（显式间隙函数版本）：**
-/
def IsDeltaWeakOWF (F : OWFFamily) (δ : Nat → ℝ) : Prop :=
  (∀ n : Nat, 0 < δ n ∧ δ n ≤ 1) ∧
    ∀ A : BitPPTAdversary,
      ∃ n0 : Nat,
        ∀ n : Nat, n ≥ n0 →
          inversionSuccessProb F A n ≤ 1 - δ n

/--
**strong OWF 定义：**
任意 PPT 反演器的成功概率关于安全参数是可忽略函数。
-/
def IsStrongOWF (F : OWFFamily) : Prop :=
  ∀ A : BitPPTAdversary,
    IsNegligible (fun n => inversionSuccessProb F A n)

/-- PPT 反演器别名。 -/
abbrev Inverter : Type 1 :=
  BitPPTAdversary

/-- 成功概率符号 `Pr`。 -/
noncomputable def Pr (F : OWFFamily) (A : Inverter) (n : Nat) : ℝ :=
  inversionSuccessProb F A n

/-- 失败概率符号 `PrFail`。 -/
noncomputable def PrFail (F : OWFFamily) (A : Inverter) (n : Nat) : ℝ :=
  failureProb F A n

-- 确保证明和重写可以使用这些短记号等价替换
theorem Pr_eq_inversionSuccessProb
    (F : OWFFamily) (A : Inverter) (n : Nat) :
    Pr F A n = inversionSuccessProb F A n := rfl

theorem PrFail_eq_failureProb
    (F : OWFFamily) (A : Inverter) (n : Nat) :
    PrFail F A n = failureProb F A n := rfl

end SecurityGames

end OneWayFunction
