# The Fasto Compiler (v1.0, 2025-04-27)

This is the compiler for the Fasto programming language.  The source
code resides in the `Fasto` directory.

Note that you need the .NET 9.0 SDK (*not* a Mono-based F#) installed
on your machine, with the `dotnet` executable in your search path.
Additionally, you should have `bash` to execute the various test
scripts, and the Java Runtime Environment (full SDK not needed) to run
the RARS simulator.

To build the compiler, run `make` (or just `dotnet build -v d Fasto`).
(The `-v d` makes FsYacc print warnings about ambiguous grammars,
which almost always require further attention.)

To interpret, compile, or optimize a Fasto program, run `bin/fasto.sh`.

To execute a compiled program (in RISC-V assembly), run `bin/rars.sh`.

To compile and immediately execute a Fasto program, run `bin/compilerun.sh`.

To run all tests from the `tests` directory (or some other), run
`bin/runtests.sh`. Use `-i` to run in interpreted mode, and `-o` to
turn on the optimizations in the compiler.
