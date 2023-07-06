# LLVM Backend

The LLVM backend is an experimental compiler backend for Lean4,
which enables code generation for a variety of targets using the
[LLVM Compiler Infrastructure](https://llvm.org/).

To build the LLVM backend, perform the following steps:

1. Install `llvm-15`. This can either be done from your package manager or by
   building it from source.
   Compiling from source requires the following steps:
   1. Obtain the source code from [https://github.com/llvm/llvm-project](https://github.com/llvm/llvm-project)
      and check out the tag `llvmorg-15.0.7`
   2. Configure the build via `cmake`. A minimum set of flags to make it
      succeed on an x86 machine would be:
      ```
      cmake -S llvm -B build -G Ninja -DLLVM_ENABLE_PROJECTS="clang" -DLLVM_TARGETS_TO_BUILD=X86 -DCMAKE_BUILD_TYPE=Release -DLLVM_LINK_LLVM_DYLIB=ON -DCMAKE_INSTALL_PREFIX=/my/prefix/llvm-15
      ```
      It is important to compile clang from source as well to avoid a situation
      where your system has a newer variant of clang that outputs bitcode
      (`lean_runtime.bc`) which the variant that we are compiling Lean with
      does not understand anymore.
   3. Compile and install via `ninja -C build install`
   4. Set your `$PATH`: `export PATH=/my/prefix/llvm-15/bin:$PATH`
2. Build lean with the extra cmake flags:

```
CXX=clang++ CC=clang cmake -DLLVM=ON -DLLVM_CONFIG=$(which llvm-config-15)  -DCMAKE_CXX_COMPILER=$(which clang++) path/to/lean4
```

3. Use the `stage2` build of lean with the extra compiler flags:

```
$ lean --bc=<bitcode-file-name> <input.lean>
-- NOTE: the file <bitcode-file-name>.linked.bc.o is automatically created
-- by the Lean compiler.
$ leanc -o <filename>.out  <bitcode-file-name>.linked.bc.o
$ ./filename.out
```

## The issue with `Lean.Compiler.IR.LLVMBindings`
Importing `Lean.Compiler.IR.LLVMBindings` will cause the binary to look for
symbols from LLVM because it wants to use FFI functions from `src/library/compiler/llvm.cpp`
which in turn call into the LLVM C API.  However `leanc` is right now not aware
of LLVM shared library that the Lean compiler ships in its installation, this
will hence fail to link for now.
