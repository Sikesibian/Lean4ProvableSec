import Mathlib.Computability.TuringMachine.StackTuringMachine
import Mathlib.Computability.StateTransition
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic

/-!
# 密码学图灵机接口 / Crypto TM Interface

## 目的 / Purpose
- 基于 Mathlib 的 `Turing.TM2` 模型，提供可直接用于理论密码学构造的封装层。
- provide a practical wrapper on top of Mathlib `Turing.TM2` for cryptographic constructions.

## 语法与关键字 / Syntax and Keywords
- `open Turing`：引入 `Turing` 命名空间下符号。
- `abbrev`：为复杂类型建立可读别名（如 `Machine`, `Cfg`）。
- `section ... end`：按主题组织定义，复用局部参数。
- `structure ... where`：打包机器与性质（如 `Adversary`, `PPTAdversary`）。
- 类型类参数 `[DecidableEq K]`：支持按栈索引更新函数。
- 类型类参数 `[Inhabited Λ] [Inhabited σ]`：提供初始默认状态。
- `Part α`：可能发散的部分计算语义。
- `theorem`：把结构字段性质提炼成可调用结论。

## 公式化语义 / Formal Semantics

记一步转移函数为 $\mathrm{step}$，配置为 $c$，有界执行：

$$
\mathrm{runCfgFor}(0,c)=c,
\qquad
\mathrm{runCfgFor}(n+1,c)=
\begin{cases}
c,& \mathrm{step}(c)=\mathrm{none}\\
\mathrm{runCfgFor}(n,c'),& \mathrm{step}(c)=\mathrm{some}(c')
\end{cases}
$$

多项式时间界谓词：

$$
\mathrm{IsPolynomial}(T)
\iff
\exists C,d\in\mathbb{N},\ \forall n,\ T(n)\le C(n+1)^d.
$$

PPT 停机约束（长度匹配时）：

$$
|x|=n,\ |r|=\ell(n)
\Longrightarrow
\mathrm{label}(\mathrm{runFor}(T(n),x,r))=\mathrm{none}.
$$

反演成功谓词模板：

$$
\mathrm{InvSucc}(x,r) :\iff x\in A(f(x);r).
$$
-/

namespace TuringMachine
namespace Crypto

open Turing

universe u v w z

/--
统一字母表形式，把每个栈的字母类型固定成同一个 `α`。
uniform stack alphabet, using one symbol type `α` for all stacks.
-/
abbrev SymAlphabet (K : Type u) (α : Type v) : K → Type v :=
  fun _ => α

/--
基于 Mathlib `TM2` 的机器类型别名。
machine alias based on Mathlib `TM2`.

说明 / Note:
- `K`：栈索引类型。/ stack index type.
- `Λ`：状态类型。/ state type.
- `σ`：标签类型。/ label type.
- `α`：符号类型。/ symbol type.

图灵机形式化定义：
$$
\mathrm{Machine}(K,Λ,σ,α) := Λ \to \mathrm{ \mathrm{Stmt}(\mathrm{SymAlphabet}(K,α)) \ Λ \ σ}.
$$
- 输入状态 `Λ`，输出一个 `TM2.Stmt`，描述在该状态下对各栈的读写操作、状态转移和标签输出。
- The input state `Λ` maps to a `TM2.Stmt` describing the read/write operations on stacks, state transitions, and label outputs at that state.
-/
abbrev Machine (K : Type u) (Λ : Type w) (σ : Type z) (α : Type v) : Type (max u v w z) :=
  Λ → TM2.Stmt (SymAlphabet K α) Λ σ

/--
基于 Mathlib `TM2` 的配置类型别名。
configuration alias based on Mathlib `TM2`.

说明 / Note:
- `K`：栈索引类型。/ stack index type.
- `Λ`：状态类型。/ state type.
- `σ`：标签类型。/ label type.
- `α`：符号类型。/ symbol type.

图灵机配置定义：
$$
\mathrm{Cfg}(K,Λ,σ,α) := \{ l : \mathrm{Option} \ σ, var : Λ, stk : K \to \mathrm{List} \ α \}.
$$
- `l`：当前标签（`none` 表示停机）。/ current label (`none` indicates halting).
- `var`：当前状态。/ current state.
- `stk`：当前栈内容映射。/ current stack content mapping.
-/
abbrev Cfg (K : Type u) (Λ : Type w) (σ : Type z) (α : Type v) : Type (max u v w z) :=
  TM2.Cfg (SymAlphabet K α) Λ σ

section Core

variable {K : Type u} {Λ : Type w} {σ : Type z} {α : Type v}

/--
带输入栈与随机币栈的初始配置。
initial configuration with explicit input stack and random-coins stack.

说明 / Note:
- 若 `inputStack = coinStack`，则后一次更新覆盖前一次更新。
- if `inputStack = coinStack`, the second update overwrites the first.
-/
def initCfgWithCoins [DecidableEq K] [Inhabited Λ] [Inhabited σ]
    (inputStack coinStack : K) (x r : List α) : Cfg K Λ σ α :=
  let stk0 : K → List α := fun _ => []
  let stk1 := Function.update stk0 inputStack x
  let stk2 := Function.update stk1 coinStack r
  { l := some default, var := default, stk := stk2 }

/--
执行固定步数，若机器提前停机则保持当前配置不再变化。
bounded-step execution; once halted, the configuration is kept unchanged.
-/
def runCfgForSteps (M : Machine K Λ σ α) [DecidableEq K] : Nat → Cfg K Λ σ α → Cfg K Λ σ α
  | 0, c => c
  | n + 1, c =>
      match TM2.step M c with
      | none => c
      | some c' => runCfgForSteps M n c'

/--
带输入与随机币的“运行到停机”语义，输出来自指定输出栈。
run-to-completion semantics with input and random coins; output is read from a chosen stack.
-/
def evalWithCoins (M : Machine K Λ σ α) [DecidableEq K] [Inhabited Λ] [Inhabited σ]
    (inputStack coinStack outputStack : K) (x r : List α) : Part (List α) :=
  (StateTransition.eval (TM2.step M)
      (initCfgWithCoins inputStack coinStack x r)).map (fun c => c.stk outputStack)

end Core

/--
敌手机器封装（确定性 TM2 + 外部随机币输入）。
adversary wrapper (deterministic TM2 + external random-coins input).

说明 / Note:
- `inputStack`：敌手的输入栈索引。/ adversary's input stack index.
- `coinStack`：敌手的随机币栈索引。/ adversary's random coins stack index.
- `outputStack`：敌手的输出栈索引。/ adversary's output stack index.
- `machine`：敌手的 TM2 机器定义。/ adversary's TM2 machine definition.

- 该结构允许灵活指定敌手的输入、随机币和输出位置，同时封装机器定义，便于后续构造和分析。
- This structure allows flexible specification of the adversary's input, random coins, and output locations, while encapsulating the machine definition for convenient construction and analysis.

使用方式 / Usage:
- 定义一个 `Adversary` 实例，指定其 `machine` 和相关栈索引。
- Define an `Adversary` instance by specifying its `machine` and relevant stack indices.
- 使用 `Adversary.run` 或 `Adversary.runFor` 来获取敌手在特定输入和随机币下的输出或配置。
- Use `Adversary.run` or `Adversary.runFor` to obtain the adversary's output or configuration under specific input and random coins.
-/
structure Adversary (K : Type u) (Λ : Type w) (σ : Type z) (α : Type v) where
  machine : Machine K Λ σ α
  inputStack : K
  coinStack : K
  outputStack : K

namespace Adversary

variable {K : Type u} {Λ : Type w} {σ : Type z} {α : Type v}

/--
敌手在给定输入与随机币下运行到停机的输出。
adversary output on fixed input and random coins (run-to-completion).
-/
def run (A : Adversary K Λ σ α) [DecidableEq K] [Inhabited Λ] [Inhabited σ]
    (x r : List α) : Part (List α) :=
  evalWithCoins (K := K) (Λ := Λ) (σ := σ) (α := α)
    A.machine A.inputStack A.coinStack A.outputStack x r

/--
敌手在给定步数内的配置。
adversary configuration after a bounded number of steps.
-/
def runForSteps (A : Adversary K Λ σ α) [DecidableEq K] [Inhabited Λ] [Inhabited σ]
    (steps : Nat) (x r : List α) : Cfg K Λ σ α :=
  runCfgForSteps (K := K) (Λ := Λ) (σ := σ) (α := α)
    A.machine steps (initCfgWithCoins (K := K) (Λ := Λ) (σ := σ) (α := α) A.inputStack A.coinStack x r)

end Adversary

/--
自然数函数的简化多项式有界定义。
lightweight polynomial upper-bound predicate on `Nat → Nat`.
-/
def IsPolynomial (f : Nat → Nat) : Prop :=
  ∃ C d : Nat, ∀ n : Nat, f n ≤ C * (n + 1) ^ d

/--
PPT 敌手接口。
PPT adversary interface.

解释 / Interpretation:
- `coinLength n`：安全参数 `n` 下随机币长度。/ random coins length at security parameter `n`.
- `timeBound n`：安全参数 `n` 下的步数上界。/ step bound at security parameter `n`.
- `halts_timeBound`：长度匹配时，机器在该步数上界内停机。/ halts within the step bound when lengths match.

- 该结构封装了一个满足多项式时间停机约束的敌手机器定义，适用于理论密码学中的安全定义和证明。
- This structure encapsulates a machine definition that satisfies a polynomial-time halting constraint, suitable for security definitions and proofs in theoretical cryptography.

使用方式 / Usage:
- 定义一个 `PPTAdversary` 实例，指定其 `adv`、`coinLength` 和 `timeBound`。
- Define a `PPTAdversary` instance by specifying its `adv`, `coinLength`, and `timeBound`.
- 使用 `PPTAdversary.run` 来获取敌手在特定输入和随机币下的输出语义。
- Use `PPTAdversary.run` to obtain the adversary's output semantics under specific input and random coins.
- 使用 `PPTAdversary.halts_at_bound` 定理来验证敌手在时间界内停机的性质。
- Use the `PPTAdversary.halts_at_bound` theorem to verify the property of halting within the time bound for the adversary.
-/
structure PPTAdversary (K : Type u) (Λ : Type w) (σ : Type z) (α : Type v)
    [DecidableEq K] [Inhabited Λ] [Inhabited σ] where
  adv : Adversary K Λ σ α
  coinLength : Nat → Nat
  timeBound : Nat → Nat
  timeBoundPoly : IsPolynomial timeBound
  haltsAtBound :
    ∀ n (x r : List α),
      x.length = n →
      r.length = coinLength n →
      (adv.runForSteps (timeBound n) x r).l = none

namespace PPTAdversary

variable {K : Type u} {Λ : Type w} {σ : Type z} {α : Type v}
variable [DecidableEq K] [Inhabited Λ] [Inhabited σ]

/--
PPT 敌手运行到停机的输出语义。
run-to-completion output semantics for a PPT adversary.
-/
def run (A : PPTAdversary K Λ σ α) (x r : List α) : Part (List α) :=
  A.adv.run x r

/--
PPT 敌手在其时间界内停机的直接实例化版本。
instantiated bounded-halting fact at the machine time bound.
-/
theorem halts_at_bound (A : PPTAdversary K Λ σ α)
    (n : Nat) (x r : List α)
    (hx : x.length = n) (hr : r.length = A.coinLength n) :
    (A.adv.runForSteps (A.timeBound n) x r).l = none :=
  A.haltsAtBound n x r hx hr

end PPTAdversary

/--
打包的比特串普通敌手。
此时 K, Λ, σ 成为了结构的内部字段，不再对外暴露为泛型参数。
-/
structure BitAdversary where
  K : Type
  Λ : Type
  σ : Type
  [decK : DecidableEq K]
  [inhΛ : Inhabited Λ]
  [inhσ : Inhabited σ]
  adv : Adversary K Λ σ Bool

/--
打包的比特串 PPT 敌手。
它自我包含了一个合法的图灵机定义以及所有类型约束。
-/
structure BitPPTAdversary where
  K : Type
  Λ : Type
  σ : Type
  [decK : DecidableEq K]
  [inhΛ : Inhabited Λ]
  [inhσ : Inhabited σ]
  adv : Adversary K Λ σ Bool
  coinLength : Nat → Nat
  timeBound : Nat → Nat
  timeBoundPoly : IsPolynomial timeBound
  haltsAtBound :
    ∀ n (x r : List Bool),
      x.length = n →
      r.length = coinLength n →
      -- 显式调用内部打包的实例以通过类型校验
      (@Adversary.runForSteps K Λ σ Bool adv decK inhΛ inhσ (timeBound n) x r).l = none

namespace BitPPTAdversary

/-- 隐藏类型类推导的敌手执行函数。 -/
def run (A : BitPPTAdversary) (x r : List Bool) : Part (List Bool) :=
  @Adversary.run A.K A.Λ A.σ Bool A.adv A.decK A.inhΛ A.inhσ x r

theorem halts_at_bound (A : BitPPTAdversary) (n : Nat) (x r : List Bool)
    (hx : x.length = n) (hr : r.length = A.coinLength n) :
    (@Adversary.runForSteps A.K A.Λ A.σ Bool A.adv A.decK A.inhΛ A.inhσ (A.timeBound n) x r).l = none :=
  A.haltsAtBound n x r hx hr

end BitPPTAdversary

section ProbabilisticSemantics

def allCoins (n : Nat) : Finset (List Bool) :=
  (Finset.univ : Finset (Fin n → Bool)).image List.ofFn

namespace BitPPTAdversary

/-- 计算 PPT 敌手在输入 x 下，输出特定结果 y 的确切概率。 -/
noncomputable def probOutput (A : BitPPTAdversary) (x y : List Bool) : ℝ :=
  by
  classical
  exact
    let n := x.length
    let coins := allCoins (A.coinLength n)
    let totalCoins := coins.card
    if totalCoins = 0 then 0 else
      let successCoins := coins.filter (fun r =>
        match Part.toOption (A.run x r) with
        | Option.some res => res = y
        | Option.none => false
      )
      (successCoins.card : ℝ) / (totalCoins : ℝ)
/-- 计算 PPT 敌手 A 在输入 x 下，其输出满足特定谓词 P 的概率。 -/
noncomputable def probEvent (A : BitPPTAdversary) (x : List Bool) (P : List Bool → Prop) [DecidablePred P] : ℝ :=
  by
  classical
  exact
    let n := x.length
    let coins := allCoins (A.coinLength n)
    let totalCoins := coins.card
    if totalCoins = 0 then 0 else
      let successCoins := coins.filter (fun r =>
        match Part.toOption (A.run x r) with
        | Option.some res => P res
        | Option.none => false
      )
      (successCoins.card : ℝ) / (totalCoins : ℝ)

end BitPPTAdversary
end ProbabilisticSemantics

end Crypto
end TuringMachine
