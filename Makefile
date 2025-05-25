.PHONY: all clean

all:
	@ dune build --no-print-directory

clean:
	@ git clean -fdX
