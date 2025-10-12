.global _start
_start:
    addi a0, zero, 0x3FF
    addi a1, zero, 0x3C3
    addi a2, zero, -61 # 0xFC3
    addi a3, zero, -1
    addi a4, zero, 3
    addi a5, zero, 5
    addi a6, zero, 123
    #
    add t0, t0, a0
    xor t0, t0, a1
    xor t0, t0, a1
    or t0, t0, a2
    and t0, t0, a0
    slt t1, t0, a3
    slt t1, t0, zero
    slt t1, t0, a6
    sltu t1, t0, a3
    sltu t1, t0, zero
    sltu t1, t0, a6
    srl t0, t0, a4
    sll t0, t0, a5
    add t1, t1, a3
    slt t1, t0, a3
    slt t1, t0, zero
    slt t1, t0, a6
    sltu t1, t0, a3
    sltu t1, t0, zero
    sltu t1, t0, a6
    srl t1, t1, a4
    