# There's more than one way to skin a cat


The skin file contains

* a list of aliases
* abstract syntax declarations for the skin AST
* a list of typed tokens to be used in the grammar
* a grammar with semantic actions that create values of the skin AST

The J file contains AST definitions.
We assume a tool extracts the AST constructors from a class file or Java source file and generates a J file.

The matcher

* matches the J AST constructors with the skin AST constructors
  * matching should create glue code to transform the skin AST constructor invocation into a J AST expression



* if a J AST constructor cannot be matched, a new skin AST constructor is created... this is just a thin wrapper around the J AST since we just need to translate back to J
* for each new skin AST constructor, a grammar rule is created
* for each skin AST constructor for which there is no J AST constructor, the rules that create that constructor are removed


AFTER THIS POINT should only deal with J ASTs

To create a grammar rule from a skin AST constructor.

* find all rules that are a supertype of the skin AST
* match each of the semantic actions (skin AST constructor calls) against the new skin AST
* find the closest good match
* copy and adapt the rule and the semantic action
* if there isn't a good match, create a new rule of the form "keyword Exp Exp ... Exp" or similar.

To generate new keywords:

* take each existing keyword, match against existing J AST nodes. if found, see if substituting the new keyword fits the pattern

## Installing

    brew install glpk
    cabal install
