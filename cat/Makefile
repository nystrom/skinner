default: ruby

java:
	cabal run cat glue/java.skin glue/ast.in 2>&1

ruby:
	cabal run cat glue/ruby.skin ast.in 2>&1

debug:
	cabal run cat-profiling +RTS -xc -RTS glue/java.skin glue/ast.in 2>&1

prof:
	cabal run cat-profiling glue/java.skin glue/ast.in 2>&1

clean:
	cabal clean
