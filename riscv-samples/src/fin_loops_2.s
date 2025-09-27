.global _start
_start:
    addi t0, zero, 3
loop2:
    addi t0, t0, -1
    blt zero, t0, loop2
    nop
