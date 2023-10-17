# Invoke `make` to build, `make clean` to clean up, etc.

.PHONY: all clean

default: all test

# Build one library and one standalone executable that implements
# multiple subcommands and uses the library.
# The library can be loaded in utop for interactive testing.
# The flag "--profile release" is passed to avoid warnings-as-errors

all:
	echo "(lang dune 2.9)\n(name project)\n(using menhir 2.1)" > dune-project
	dune build --profile release @install 
	@test -L main.native || ln -s _build/install/default/bin/main.native main.native

test: main.native
	echo "(lang dune 2.9)\n(name project)\n(using menhir 2.1)" > dune-project
	./main.native --test

# Clean up
clean:
	echo "(lang dune 2.9)\n(name project)\n(using menhir 2.1)" > dune-project
# Remove files produced by dune.
	dune clean
# Remove remaining files/folders ignored by git as defined in .gitignore (-X).
	git clean -dfXq

utop:
	echo "(lang dune 2.9)\n(name project)\n(using menhir 2.1)" > dune-project
	dune utop . --profile release
