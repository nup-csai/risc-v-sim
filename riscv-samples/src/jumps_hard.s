.global _start
_start:
    la t0, routine1
    la t1, routine2
    jalr ra, 4(t0)
    j routine3
routine1:
    nop
    mv t3, ra
    jalr ra, t1, 0
    mv ra, t3
    ret
routine2:
    ret
routine3:
