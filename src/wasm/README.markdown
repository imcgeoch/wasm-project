# README

This package implements the [WASM Specification](https://webassembly.github.io/spec/).
The package structure is made to mirror the specification structure as much as
possible.

## The `wasm` Package
The `wasm` package can be built/checked with the following respective commands.

```bash
$ idris --build wasm.ipkg      # Compile package to bytecode
$ idris --checkpkg wasm.ipkg   # Check the package
```

These are useful to ensure changes aren't breaking.

## `Structure`
This maps out the basic syntax and types of WASM as defined in the
[Structure](https://webassembly.github.io/spec/core/syntax/index.html) section
of the specification.

## `Execution`
This defines the runtime execution of WASM as defined in the [Execution](https://webassembly.github.io/spec/core/exec/index.html)
section of the specification.
