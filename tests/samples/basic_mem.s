.global _start
_start:
    # Add 1Kb to PC
    auipc t0,1
    addi t1, t1, 25
    sw t1, 120(t0)
    lw t1, 120(t0)
    addi t2, t1, 15
    sw t2, 128(t0)
    lw t2, 128(t0)
 