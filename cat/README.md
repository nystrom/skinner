# There's more than one way to skin a cat

To build:

    cd cat
    cabal install --dependencies-only
    cabal configure
    cabal build

To run:

    cabal run java.skin ast.in

