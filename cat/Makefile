all:
	cabal run cat java.skin ast.in 2>&1

debug:
	cabal run cat-profiling +RTS -xc -RTS java.skin ast.in 2>&1

prof:
	cabal run cat-profiling java.skin ast.in 2>&1

clean:
	cabal clean
