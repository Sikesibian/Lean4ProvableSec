-- This module serves as the root of the `ProvableSec` library.
-- Import modules here that should be built as part of the library.
import ProvableSec.Defination.Baisc.TuringMachine.TMbasic
import ProvableSec.Defination.Baisc.TuringMachine.TMCrypto
import ProvableSec.Defination.Baisc.Complexity.ComplexityClass
import ProvableSec.Defination.OneWayFunction.owfBasic
import ProvableSec.Defination.CryptoNotation
import ProvableSec.ClassicTheorem.OWF.YaoTheorem
import ProvableSec.Examples

/-!
# ProvableSec Root Module

## 模块说明 / Module Description
- 中文：该文件是库根模块，负责汇总导入所有需要随库一起构建的子模块。
- English: this is the root module aggregating library imports.

## 语法与关键字 / Syntax and Keywords
- `import`：导入子模块到当前命名空间上下文。
- `--`：单行注释，通常用于简短开发说明。

## 维护建议 / Maintenance Notes
- 新增 `.lean` 子模块后，建议第一时间在此处加入 `import`，避免遗漏构建检查。
-/
