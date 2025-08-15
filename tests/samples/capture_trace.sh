# This script is for being run inside the integration test container.
# Please see tests/vs_gdb.rs

FILE=$1
NSTEPS=$2

# /tmp/cmds is the file with the commands which are going 
# to pump into the GDB shell.
# Basic setup so GDB knows what it is going to debug.
TMP=""
read -r -d '' TMP <<EOM
file /tmp/program
target remote localhost:1234
set architecture riscv:rv64
set pagination off
b *0x80000000
continue
EOM
echo "$TMP" > /tmp/cmds

# Even when you pass -bios none, Qemu inserts a smplistic
# boot-loader into its "ROM" segment and starts the
# execution there. That boot-loader sets t0, a2 and a2
# to some handy values. Let's zero them out.
TMP=""
read -r -d '' TMP <<EOM
set \$t0 = 0x0
set \$a1 = 0x0
set \$a2 = 0x0
info registers
EOM
echo "$TMP" >> /tmp/cmds

for i in $(seq 1 $NSTEPS); 
do
TMP=""
read -r -d '' TMP <<EOM
stepi
printf "\n===NEXT\n"
info registers
EOM
echo "$TMP" >> /tmp/cmds
done

read -r -d '' TMP <<EOM
printf "\n===END\n"
quit
EOM
echo "$TMP" >> /tmp/cmds

# We don't set -e at the very start, because
# read actually exists with non-zero code.
# Past that point we definitely want to exit
# if next commands exit with non-zero code.
set -e

cd /ws
# Compile and link
riscv64-linux-gnu-as $FILE -o /tmp/obj
riscv64-linux-gnu-ld -Ttext=0x80000000 /tmp/obj -o /tmp/program
# Start the VM and capture the trace with GDB.
# We do not kill qemu, because it will be killed when the
# container (this script pretty much) exits.
qemu-system-riscv64 -machine virt -bios none -kernel /tmp/program -s -S -nographic &
gdb-multiarch --batch -x /tmp/cmds
# Hand over the compiled program
cp /tmp/program "/elfs/$FILE.elf"
