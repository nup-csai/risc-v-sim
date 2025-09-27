.global _start
_start:
    addi t0, zero, 3
loop3:
    addi t0, t0, -1
    bltu zero, t0, loop3
    nop
