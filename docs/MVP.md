# The MVP of the project

## What is this
* This is the basic baseline project to check if the
  idea is worth it
* It is expected to be finished in a relatively short
  amount of time

## Features of the MVP
* Accepting an `.elf` file
* Support of all registers from `rv32i`
* Support of the following instructions:
    - Adding
    - Loading values
* Locating an entry point and running the
  program from there until the intepreter
  runs out of range
* When the intepreter exits -- print machine state (all registers)

## Usage example

```bash
intepreter program.elf
```

Will lead to something like (register listing is not full for briefity)

```
Machine halted (PC out of executable range).

register    ABI-name    value
=============================
PC          n/a         0x80215
x0          zero        0x0
x1          ra          0x124
x2          sp          0x1263
x3          gp          0x3524
```

```
Machine halted (PC reached an undecodable instruction).

PC is pointing at `0x14241531`, which is not a valid instruction

register    ABI-name    value
=============================
PC          n/a         0x80215
x0          zero        0x0
x1          ra          0x124
x2          sp          0x1263
x3          gp          0x3524
```