.global _start
_start:
    addi t0, zero, 3
loop4:
    addi t0, t0, -1
    slt t1, zero, t0
    bne t1, zero, loop4
    nop
