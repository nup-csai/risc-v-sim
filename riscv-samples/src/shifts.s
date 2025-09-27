.global _start
_start:
    addi t0, t0, 0x3FF
    xori t0, t0, 0x3C3
    xori t0, t0, 0x3C3
    ori t0, t0, -61 # 0xFC3
    andi t0, t0, 0x3FF
    slti t1, t0, -1
    slti t1, t0, 0
    slti t1, t0, 123
    sltiu t1, t0, -1
    sltiu t1, t0, 0
    sltiu t1, t0, 123
    srli t0, t0, 3
    slli t0, t0, 5
    addi t1, t1, -1 # 0xFFF
    slti t1, t0, -1
    slti t1, t0, 0
    slti t1, t0, 123
    sltiu t1, t0, -1
    sltiu t1, t0, 0
    sltiu t1, t0, 123
    srli t1, t1, 3
    