# Project's Scope

## Goals

It is assumed that an average computer architecture course covers
the following topics:
* Basic instructions
* Registers
* Jumping
* Working with memory
* ecalls (system calls)
* Interrupts
* The behaviour of the intepreter should closely match the
  behaviour of QEMU with the same program
    - This can be ensured with a comptent CI
* Make the program embdeddable into automation stuff like CI
    - This can be done implementing the flag, that lets the
      intepreter output its results in JSON format instead
      of something human readable

Therefore project goals are
* Provide an easy-to-use tool to run RiscV programs
* Provide informative errors for the user
* Run a RiscV containing `.elf` file
* Program trace construction
* Highly configurable limits of what a program can do (adress space limitation)
* High safety
* Lightweightness (small program size, high performance)
* All RiscV features needed to cover in an average Computer
  Architecture course

## Non-Goals (and why)

* Asm source intepreter
    - Doing this will move the project too far from reality.
      Students should get familiar with compiling programs and acquire
      basic familarity with `.elf` files
* Support for multiple cores
    - Parallel programming is a complicated topic, far out of
      any computer architecture course curricvulum. RiscV's memory
      model is complex, emulating all of its quirks is not worth it
* Dynamic linking
    - Dynamic linking is a subject discussed on Operating Systems, it
      is complex and outside of Computer Architecture curricvulum
* Priveleged code execution
    - This feature is complex and seems to be uncommon in Computer
      Architecture courses
* Creating a brand-new RiscV VM
    - There are other projects for that like qemu
* High precision emulation of a RiscV CPU
    - Getting closely familiar with caches and other things is far
      out of Computer Architecture I curricvulum

# Features

## Must-Haves

* Running `.elf` files
* Resolving symbols from `.elf`
* Highly user-friendly error messages and warnings
* Defining what adresses the "machine" can access and how
    - Note that this is not PMP. These would be rules enforced by the
      runtime and won't be accessible by the code at any point in time
* Full support of the `rv32i` instruction set
* Randomization of the unintialised memory bytes
    - It is better to make the environment close to the real world as
      possible. Some of program segments are NOT initialised. Therefore
      they shouldn't be zeroed
* Program tracing
* Memory dumping
* Alternative machine-readable result format

## Could-Haves

* Support for `M`, `F` and `D` extensions
* Support for vector instructions
    - Introducing students to SIMD instructions might be useful, but
      probably not necessary
* PMP registers
* Priveleged execution
* Trap support
* Defining what instructions can be used
    - This can be useful to design a checker for simple tasks like
      "implement multiplication"
* Support for `rv64`
* Recognition of the pseudo-instructions
    - Using debug information to properly format the assembly is very
      useful as this helps newcomers associate their code with the program
      trace better

## Wont-Haves

* Multiple core support
* Compressed instructions
* Support for extensions not mentioned in "Could-Haves"
    - All of them are either complicated, unstable or super specific