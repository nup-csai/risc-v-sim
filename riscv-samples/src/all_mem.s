.global _start
_start:
    # Add 1Kb to PC
    auipc t0,1
    addi t0, t0, 128
    addi t1, t1, 25
    sb t1, -128(t0)
    sh t1, 136(t0)
    sw t1, 120(t0)
    lw t1, 120(t0)
    lh t1, 136(t0)
    lhu t1, 136(t0)
    lb t1, -128(t0)
    lbu t1, 136(t0)
    addi t2, t1, 15
    sb t2, 128(t0)
    sh t2, 136(t0)
    sw t2, 120(t0)
    lw t2, 120(t0)
    lh t2, 136(t0)
    lhu t2, 136(t0)
    lb t2, 128(t0)
    lbu t2, 136(t0)
 