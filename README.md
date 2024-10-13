## What Is This?

### The Problem I

When teaching computer architecture one of the most important parts
is introducing the students to assembly coding. RiscV assembly is one
of the best candidates for that, since it is RISC and has much more
intuitive semantics compared to x86 assembly.

However, assembly in addition to learning a new programming language
has the following tough challenges for newcomers:

* Lack of runtime checks
* Lack of informative feedback of what the user did wrong
* Difficult to debug
* General unsafety

### The Solution

This repository provides a RiscV intepreter aimed to assist newcomers
at learning assembly coding.

### Why Rust

Such project as this would highly benefit from a language with following
properties:
* Memory safety
* Speed comparable to C
* Strong type system
* High performance
* Statically linked all-included binaries
* Simple-to-use & easily reproducible build system

Rust fits all these criterias