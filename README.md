# There's more than one way to skin a cat

Skinner takes an AST description and a language skin description 
and generates a JavaCUP and JFlex parser/lexer for a language
that constructs the given ASTs.

In this way, given an AST class hierarchy, you can 
generate a parser for a language that's Java-like or
Ruby-like or JavaScript-like, etc.

## To use

Skinner is still a work-in-progress.

The `cat` directory contains the code (in Haskell) of the skinner
itself.

The `glue` directory contains:

- the Skin files (currently just Java and Ruby)
- a Python script for generating the lexer 
- Java code for the runtime library (mostly for the lexer)
- some tests
