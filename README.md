# Ocaml-Compiler


• Reads the contents of the Scheme source file into a string.

• Prepends the content of stdlib.scm to the string.

• Reads the expressions in the string, using the reader you wrote in assignment 1, returning a
list of sexprs.

• Tags the list of sexprs using the tag parser you wrote in assignment 2, returning a list of
exprs.

• Applies to each expr in the above list the run_semantics procedure you wrote in assignment
3, returning a list of expr’s.

• Constructs the constants table, and the free-variables table.

• Calls generate to generate a string of x86-64 assembly instructions for every expr’.

• Adds a prologue and epilogue to the string, so that it becomes a self-contained assembly
language program.

• Outputs the string containing the assembly language program
