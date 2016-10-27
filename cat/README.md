# There's more than one way to skin a cat

To build:

    cd cat
    cabal install --dependencies-only
    cabal configure
    cabal build

To run:

    cabal run cat glue/java.skin glue/test2-java/ast.in

