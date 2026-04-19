import ProvableSec

/-!
# Main Executable Module

## 模块说明 / Module Description
- 中文：该文件提供最小可执行入口，用于验证库导入和运行链路。
- English: minimal executable entry point for import and runtime sanity checks.

## 语法与关键字 / Syntax and Keywords
- `def`：定义常量与函数。
- `IO Unit`：无返回值的 I/O 程序类型。
- `IO.println`：控制台输出。
- `s!"..."`：字符串插值语法。
- `#eval`：在 Lean 环境中直接求值表达式。
-/

def hello : String := "Provable Security in Lean 4"

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"

#eval main
