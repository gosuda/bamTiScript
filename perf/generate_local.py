"""Generate deterministic local compiler and runtime comparison workloads."""

from __future__ import annotations

import argparse
from pathlib import Path


def write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    root: Path = args.output
    width = 512
    properties = "".join(f"  p{index:04}: number;\n" for index in range(width))
    functions: list[str] = []
    for function in range(8):
        accesses = "".join(
            f"  sum += value.p{(function * 256 + index) % width:04};\n"
            for index in range(256)
        )
        functions.append(
            f"export function sumProperties{function}(value: Wide): number {{\n"
            f"  let sum: number = 0;\n{accesses}  return sum;\n}}\n"
        )
    write(
        root / "wide_properties.ts",
        f"interface Wide {{\n{properties}}}\n" + "".join(functions),
    )
    graph = root / "graph"
    imports: list[str] = []
    exports: list[str] = []
    for module in range(32):
        name = f"Module{module}"
        write(
            graph / f"module{module}.ts",
            f"export interface {name} {{\n{properties}}}\n"
            f"export function read{module}(value: {name}): number {{\n"
            "  return value.p0000 + value.p0256 + value.p0511;\n}\n",
        )
        imports.append(f'import {{ read{module} }} from "./module{module}";\n')
        exports.append(f"read{module}")
    write(graph / "main.ts", "".join(imports) + f"export {{ {', '.join(exports)} }};\n")
    write(
        root / "property_loop.ts",
        "const item = { a: 1, b: 2, c: 3, d: 4, e: 5, f: 6, g: 7, h: 8 };\n"
        "let checksum: number = 0;\n"
        "for (let index: number = 0; index < 100000; index++) {\n"
        "  checksum += item.a + item.b + item.c + item.d;\n"
        "  checksum += item.e + item.f + item.g + item.h;\n"
        "}\n"
        "process.stdout.write(`${checksum}\\n`);\n",
    )
    write(root / "property_loop.stdout", "3600000\n")
    write(
        root / "allocation_churn.ts",
        "type Cell = { value: number; next: number };\n"
        "const survivors: Cell[] = [];\n"
        "let checksum: number = 0;\n"
        "for (let index: number = 0; index < 100000; index++) {\n"
        "  const cell: Cell = { value: index, next: index + 1 };\n"
        "  checksum += cell.value;\n"
        "  if (index % 100 === 0) survivors.push(cell);\n"
        "}\n"
        "for (let index: number = 0; index < survivors.length; index++) {\n"
        "  checksum += survivors[index].next;\n"
        "}\n"
        "process.stdout.write(`${checksum}\\n`);\n",
    )
    write(root / "allocation_churn.stdout", "5049901000\n")
    print(root.resolve())


if __name__ == "__main__":
    main()
