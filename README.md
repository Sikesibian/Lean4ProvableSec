# ProvableSec

ProvableSec 是一个在 Lean 4 中探索可证明安全接口化的项目。我们还在持续迭代，很多证明与工程细节仍在完善中。

## 目前亮点

- 把机器语义层与密码学语义层做了分离，结构比早期清晰。
- 提供贴近教材的基础记号：`Pr`、`PrFail`、`Weak`、`Strong`。
- OWF 基础定义、符号层与示例模块已经连通，便于后续扩展经典定理。

## 本次调整

最近做了一次接口层重构。

过去：很多地方需要反复显式指定上下文参数 `K`、`Λ`、`σ`。

现在：常用接口已经做了封装，日常使用通常不需要再手写 `(K := ...) (Λ := ...) (σ := ...)`。

这次调整的目标很朴素：减少样板参数，让注意力更多回到安全定义和证明思路本身。

## 快速开始

```bash
lake update
lake build
lake exe provablesec
```

在其他 Lean 文件中使用本库：

```lean
import ProvableSec
```

## 主要模块（精简版）

> 说明：仓库实际路径保留历史拼写 `Defination`、`Baisc`。

| 模块 | 作用 |
|---|---|
| `ProvableSec/Defination/Baisc/TuringMachine/TMbasic.lean` | DTM/NTM 基础语义 |
| `ProvableSec/Defination/Baisc/TuringMachine/TMCrypto.lean` | 敌手与 PPT 接口 |
| `ProvableSec/Defination/OneWayFunction/owfBasic.lean` | OWF 基础定义 |
| `ProvableSec/Defination/CryptoNotation.lean` | 密码学记号与封装接口 |
| `ProvableSec/ClassicTheorem/OWF/YaoTheorem.lean` | Yao 相关构造占位与接口 |

## 最小示例

```lean
import ProvableSec.Defination.CryptoNotation

open ProvableSec.CryptoNotation
open scoped CryptoNotation

variable (F : OWFFamily)
variable (A : Inverter)
variable (n : Nat)

example : PrFail[F](A, n) = 1 - Pr[F](A, n) := by
  exact OneWayFunction.PrFail_eq_failureProb F A n
```

## 说明

- 项目仍在重构期，接口后续可能继续微调。
- 若新增定义后下游仍提示找不到常量，可先执行一次 `lake build` 刷新产物。
- 欢迎指出问题与建议，我们会持续改进。
