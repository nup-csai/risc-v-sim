.global _start
_start:
    j routine4
routine1:
    j routine2
routine2:
    j routine4
routine3:
    j routine1
routine4:
    j routine3
