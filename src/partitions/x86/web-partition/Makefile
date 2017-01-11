include ../toolchain.mk

CUSTOM_MALLOC_INCLUDE=../../../../../custom_malloc/include
CUSTOM_MALLOC_SRC_PATH=../../../../../custom_malloc/src
PICOTCP_INCLUDE=../../../../../picotcp/build/include
PICOTCP_LIB_PATH=../../../../../picotcp/build/lib


CFLAGS=-m32 -c -nostdlib --freestanding -I$(LIBPIP)/include/ -I$(CUSTOM_MALLOC_INCLUDE) -I$(PICOTCP_INCLUDE)
ASFLAGS=$(CFLAGS)

LDFLAGS=-L$(LIBPIP)/lib -L$(PICOTCP_LIB_PATH) -I$(LIBPIP)/include/ -I $(PICOTCP_INCLUDE) -I$(CUSTOM_MALLOC_INCLUDE) -melf_i386 -Tlink.ld -lpip -lpicotcp
LDFLAGS2=-L$(LIBPIP)/lib -L$(PICOTCP_LIB_PATH) -I$(LIBPIP)/include/ -I $(PICOTCP_INCLUDE) -I$(CUSTOM_MALLOC_INCLUDE) -melf_i386 -Tlinkelf.ld -lpip -lpicotcp


ASSOURCES=$(wildcard *.S)
CSOURCES:=$(wildcard *.c)
ASOBJ=$(ASSOURCES:.S=.o)
COBJ=$(CSOURCES:.c=.o)
COBJ+=custom_memalloc.o stringFunctions.o
EXEC=web-partition.bin

all: $(EXEC)
	@echo Done.

clean:
	rm -f $(ASOBJ) $(COBJ) $(EXEC)

$(EXEC): $(ASOBJ) $(COBJ)
	$(LD) $^ -o $@ $(LDFLAGS)
	#$(LD) $^ -o web-partition.elf $(LDFLAGS2)

%.o: %.s
	$(AS) $(ASFLAGS) $< -o $@

%.o: %.c
	$(CC) $(CFLAGS) $< -o $@

custom_memalloc.o: $(CUSTOM_MALLOC_SRC_PATH)/custom_memalloc.c
	$(CC) -c $< -o $@ $(CFLAGS) -I $(CUSTOM_MALLOC_INCLUDE)

stringFunctions.o: $(CUSTOM_MALLOC_SRC_PATH)/stringFunctions.c
	$(CC) -c $< -o $@ $(CFLAGS) -I $(CUSTOM_MALLOC_INCLUDE)

