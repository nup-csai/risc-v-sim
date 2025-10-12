.global _start
_start:
    call routine4
routine1:
    call routine2
routine2:
    call routine4
routine3:
    call routine1
routine4:
    call routine3
