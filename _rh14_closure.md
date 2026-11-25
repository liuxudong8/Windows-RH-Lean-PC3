# RH_14 · `import` 闭包实测（纯静态）

根：`F:\F\BSD_GRH_RH\RH_14\lean\src`

起点：`src/Main.lean`（lakefile 的 `Main` roots = `["Statements","Main"]`）

## 结果

| 项 | 数 |
|---|---|
| 归档内 `.lean` 文件总数 | 175187 |
| **`Main.lean` 可达文件数** | **175187** |
| 不可达（与 RH 证明无关） | 0 |
| 闭包内 `theorem/lemma/def` | **1031574** |
| 闭包内 `*_holds` 节点 | **5659** |

外部依赖（库外根包）：`Mathlib` 156238，`Lean` 12，`Batteries` 3

## 说明

- 该闭包只按 `import` 传递性计算，不含 `open`/`exact` 层面的引用，属**上界**。
- 若数为小，G1 只需在这个集合上跑 `#print axioms`；若数为大，则须先按 gate 再筛一轮。
