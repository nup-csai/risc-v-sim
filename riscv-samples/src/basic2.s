.global _start
_start:
    xor a2, a2, a2
    addi a2, a2, 20
    xor a3, a3, a3
    addi a3, a3, 10
    sub a2, a2, a3 
    xori s1, ra, 123
    