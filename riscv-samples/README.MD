This file contains the sample programs used to test risc-v-sim against
the RiscV implementation in QEMU.

## How Does It Work
1. A program is compiled and linked into an `.elf` file by a GCC compiler
   from a RiscV toolchain.
2. The program is then run inside a QEMU RiscV implementation without bios,
   graphics or any other devices.
3. A GDB debugger is mounted onto QEMU, driving it to make N instruction steps
   and taking a snapshot of the values in the registers each step, producing
   a trace.
4. The trace and the program are then forwarded to the `vs_qemu_traces.rs`
   integration test, that parses the traces and feeds the program to the
   risc-v-sim.
5. We then check that risc-v-sim produces the same trace.

## Capturing The Traces Yourself
You do not need to repeat all thoes complicated steps yourself. To capture the 
traces:
1. Make sure you have Riscv64 toolchain with QEMU and GDB
2. Run `make capture` (DO NOT more than one concurrent `make` job)
3. For extra cleanup if something fails, run `pkill qemu`
4. For each file in `src`, there will be a corresponding trace in `traces`

## Adding Tests
The Makefile automatically takes care of building and capturing the trace for
all files located in `src`. To add one more test to the suite, do the following:
1. Add the `.s` assembly file to the `src/` folder
    - Make sure to include `.global _start` and the `_start` symbol
2. Add a file with a corresponding name to the `cfg/` folder
    - The file should contain a single number -- the number of
      steps the QEMU should take before terminating
3. You can test the process exclusively for your new test by running
```
make my_new_test.trace
```

## Testing The Tests Against RiscV-sim
1. Run `make capture` in `riscv-samples`
2. Run `cargo test --test vs_qemu_traces` in the project root