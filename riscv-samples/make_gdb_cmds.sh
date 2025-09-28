#! /bin/bash
# This file generates the commands used to drive GDB.
#
# Usage: ./make_gdb_cmds.sh FILE_TO_GENERATE_COMMANDS_FOR NUMBER_OF_STEPS

FILE=$1
NSTEPS=$2

# Even when you pass -bios none, Qemu inserts a smplistic
# boot-loader into its "ROM" segment and starts the
# execution there. That boot-loader sets t0, a2 and a2
# to some handy values. We zero these values out for
# a cleaner trace. 
cat <<EOM
file $FILE 
target remote localhost:1234
set architecture riscv:rv64
set pagination off
b *0x80000000
continue
set \$t0 = 0x0
set \$a1 = 0x0
set \$a2 = 0x0
EOM

for i in $(seq 1 $NSTEPS); 
do
cat <<EOM
stepi
info registers
printf "===NEXT\n"
EOM
done

cat <<EOM
kill
quit
EOM