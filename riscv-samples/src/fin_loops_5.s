.global _start
_start:
    addi t1, zero, 1
    addi t0, zero, 3
loop5:
    addi t0, t0, -1
    bge t0, t1, loop5
    nop
