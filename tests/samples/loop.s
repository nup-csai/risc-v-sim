.global _start
_start:
    xor a2, a2, a2
loop:
    addi a2, a2, 1
    j loop
    