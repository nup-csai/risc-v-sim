.global _start
_start:
    addi t0, zero, 3
loop1:
    addi t0, t0, -1
    bge t0, zero, loop1
    nop
