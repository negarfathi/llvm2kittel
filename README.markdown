# Extended llvm2KITTeL

This repository contains an extended version of the original [llvm2KITTeL `kou` branch](https://github.com/gyggg/llvm2kittel/tree/kou).

The extension adds LLVM-IR-to-LTS translation support for structures, arrays, and bit-level operations. It is intended for use with the [Athena](https://github.com/negarfathi/Athena) termination and non-termination analysis framework.

## Docker Image
A Docker image containing the extended implementation is available at:
```bash
docker pull negarfathi/llvm2kittel:latest
```

## Quick Start

### 1. Pull the Docker image:
```bash
docker pull negarfathi/llvm2kittel:latest
```

### 2. Start the container from the directory containing the input C program:
```bash
docker run --rm -it \
  -v "$(pwd):/work" \
  -w /work \
  negarfathi/llvm2kittel:latest \
  /bin/bash
```

### 3. Compile the input program to LLVM bitcode inside the container:
```bash
clang -Wall -Wextra -g -O0 \
  -c -emit-llvm input.c \
  -o input.bc
```
Replace `input.c` with the C source file to analyze.

### 4. Configure the translation options and run llvm2KITTeL:
```bash
SIGNEDNESS_INFO=true
UNREACHABLE_EXIT=false

llvm2kittel/build/llvm2kittel \
  --signedness-info="$SIGNEDNESS_INFO" \
  --unreachable-exit="$UNREACHABLE_EXIT" \
  --dump-ll \
  --no-slicing \
  --eager-inline \
  --t2 \
  input.bc > output.t2
```
The generated labeled transition system is written to `output.t2`.

#### Configuration Options:
- `--signedness-info` — `true` includes signedness information in the generated LTS; `false` omits it.
- `--unreachable-exit` — `true` treats reaching an unreachable state as a violation; `false` disables this behavior.

## Citation:
If you use this extended implementation or its Docker image in your research, please cite the following paper:

N. Fathi, H. Unno, T. Terauchi, and R. Purandare, “Sound Termination and Non-termination Analysis of C Programs with Bit-Precise Bounded Semantics and Advanced Constructs,” *Proceedings of the ACM on Software Engineering*, vol. 3, no. FSE, pp. 4505–4528, Jun. 2026, doi: [10.1145/3808205](https://doi.org/10.1145/3808205)
