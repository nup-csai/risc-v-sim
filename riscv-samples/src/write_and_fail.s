.global _start
_start:
    nop
    
    mv  t0, zero
    addi t0, t0, 0x48 # 0x48 == H
    sb t0, 0(zero)
    
    mv t0, zero
    addi t0, t0, 0x49 # 0x49 == I
    sb t0, 1(zero)

    # Jump to a bad address
    addi t1, t1, 0xAD 
    jalr zero, 0(t1)
