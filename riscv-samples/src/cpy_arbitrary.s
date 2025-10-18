.global _start
_start:
    nop
    addi t1, t1, 0x400
    addi t3, t3, 12
loop:
    lb t2, 0(t0)
    sb t2, 0(t1)
    addi t0, t0, 1 
    addi t1, t1, 1 
    addi t3, t3, -1
    bnez t3, loop
    ebreak
