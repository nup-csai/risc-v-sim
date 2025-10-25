.global _start
_start:
    la t0, buffer
walk_buff:
    lb t2, 0(t0)
    addi t0, t0, 1
    bnez t2, walk_buff

    la t0, buffer
    la t1, msg
copy:
    lb t2, 0(t1)
    sb t2, 0(t0)
    addi t0, t0, 1
    addi t1, t1, 1
    bnez t2, copy
nop

# Len = 10
.section .rodata
msg:
    .string "Some data"
    .byte 0

# Len = 14
.section .data
buffer:
    .string "Hello, world!"
    .byte 0