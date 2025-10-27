BINDIRS := bin bin/obj traces gdb_cmds

# The aliases for used commands. Change the names if they
# are called differently in your setup.
AS := riscv64-linux-gnu-as 
LD := riscv64-linux-gnu-ld
QEMU := qemu-system-riscv64
GDB := gdb-multiarch

LDFLAGS := -Ttext=0x80000000
LDFLAGS += -Tdata=0x80002000
LDFLAGS += -Trodata=0x80003000

# GDB output is quite machine-unfriendly and contains some junk.
# This command santizes the output to make the trace machine-friendly. 
TRACE_FILTER := awk '/^[a-z]([a-z]|[0-9])/ {print $$1 " " $$2} /^==/{print}' | grep "\S" 

SRCS = $(wildcard src/*.s)
OBJS = $(patsubst src/%,%.o,$(basename $(SRCS)))
ELFS = $(patsubst src/%,%.elf,$(basename $(SRCS)))
TRACES = $(patsubst src/%,%.trace,$(basename $(SRCS)))
GDBCMDS = $(patsubst src/%,%.gdb,$(basename $(SRCS)))

ALL_OBJS = $(addprefix bin/obj/, $(sort $(OBJS)))
ALL_ELFS = $(addprefix bin/, $(sort $(ELFS)))
ALL_TRACES = $(addprefix traces/, $(sort $(TRACES)))
ALL_GDBCMDS = $(addprefix gdb_cmds/, $(sort $(GDBCMDS)))

$(ALL_OBJS) $(ALL_ELFS) $(ALL_TRACES) $(ALL_GDBCMDS): | $(BINDIRS)

$(BINDIRS):
	mkdir -p $@

bin/obj/%.o: src/%.s
	$(AS) $< -o $@

bin/%.elf: bin/obj/%.o
	$(LD) $(LDFLAGS) $< -o $@

gdb_cmds/%.gdb: cfg/%
	bash ./make_gdb_cmds.sh bin/$*.elf $(file < cfg/$*) > $@

traces/%.trace: bin/%.elf gdb_cmds/%.gdb
	qemu-system-riscv64 -smp 1 -m 5M -machine virt -bios none -kernel bin/$*.elf -s -S -nographic &
	gdb-multiarch --batch -x gdb_cmds/$*.gdb | $(TRACE_FILTER) > $@

init-capture: cmds build

capture: $(ALL_TRACES)

cmds: $(ALL_GDBCMDS)

build: $(ALL_ELFS)

.PHONY: init-capture debvars clean traces build cmds all

clean:
	rm -rf bin
	rm -rf gdb_cmds
	rm -rf traces

debvars:
	echo $(SRCS)
	echo $(OBJS)
	echo $(ELFS)
	echo $(TRACES)
	echo $(GDBCMDS)
	echo $(ALL_GDBCMDS)
