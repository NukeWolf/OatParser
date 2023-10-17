## Using main runner

The runner `main.native` acts like the `clang` compiler. Given several
`.ll`, `.c`, and `.o` files, it will compile the `.ll` files to `.s` files
(using the module backend) and then combine the results with the `.c`
and `.o` files to produce an executable named `a.out`. You can also
compile the `.ll` files using clang instead of the default module backend,
which can be useful for testing purposes.

* To compile and `.oat` program with the runtime built-ins to an
executable `a.out`, run:
```
  ./main.native path/to/program.oat runtime.c -o a.out
```


* To run the automated test harness do:
```
  ./main.native --test
```

* To compile `.ll` files using the module backend:
```
  ./main.native path/to/foo.ll
```
  Doing so will

  - create `output/foo.s`   (backend assembly code)
  - create `output/foo.o`   (assembled object file)
  - create `a.out`          (linked executable)

 **NOTE:** by default the `.s` and `.o` files are created in 
 a directory called `output`, and the filenames are 
 chosen so that multiple runs of the compiler will
 not overwrite previous outputs.  `foo.ll` will be 
 compiled first to `foo.s` then `foo_1.s`, `foo_2.s`, etc.


* To compile `.ll` files using the clang backend:
```
  ./main.native --clang path/to/foo.ll
```

## Useful flags

```
  --print-oat
    pretty prints the Oat abstract syntax to the terminal

  --print-ll 
    echoes the ll program to the terminal

  --print-x86
    echoes the resulting .s file to the terminal

  --interpret-ll
    runs the ll file through the reference interpreter
    and outputs the results to the console

  --execute-x86
    runs the resulting a.out file natively
    (applies to either the default module backend or clang-compiled code)

  --clang compiles to assembly using clang, not the module backend

  -v
    generates verbose output, showing which commands are used
    for linking, etc.

  -op <dirname>
    change the output path [DEFAULT=output]

  -o 
    change the generated executable's name [DEFAULT=a.out]

  -S
    stop after generating .s files 

  -c 
    stop after generating .o files 

  -h or --help
    display the list of options
```

## Example uses

Run the test case `./llprograms/factrect.ll` using the module backend:

```
./main.native --execute-x86 llprograms/factrect.ll 
--------------------------------------------------------------- Executing: a.out
* a.out returned 120
```
