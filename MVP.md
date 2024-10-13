# The MVP of the project

What is this:
* This is the basic baseline project to check if the
  idea is worth it
* It is expected to be finished in a relatively short
  amount of time

Features of the MVP:
* Accepting an `.elf` file
* Support of all registers from `rv32i`
* Support of the following instructions:
    - Adding
    - Loading values
* Locating an entry point and running the
  program from there until the intepreter
  runs out of range
* When the intepreter exists -- print machine state (all registers)