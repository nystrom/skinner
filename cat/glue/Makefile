.SUFFIXES: .java .class .cup .flex

default:

test-all: test1-java test2-java test1-ruby test2-ruby

test1-java: .FORCE
	rm -f test1-java/out.cup
	(cd ..; cabal run cat glue/java.skin glue/test1-java/ast.in) | awk '/grammar/ { p = 1; next; } /<<grammar/ { p = 0 } { if (p) print }' > test1-java/out.cup
	(cd test1-java; java -cp ../java_cup.jar java_cup.Main -nopositions out.cup)
	(cd test1-java; ../make_lexer out.cup ../java.flex > out.flex)
	(cd test1-java; java -cp ../jflex.jar jflex.Main out.flex)
	(cd test1-java; javac -cp ../java_cup.jar:../jflex.jar:..:. Parser.java Lexer.java sym.java)
	(cd test1-java; javac -cp ../java_cup.jar:../jflex.jar:..:. Program.java TestJava.java)
	(cd test1-java; java -cp ../java_cup.jar:../jflex.jar:..:. TestJava test.java-skinned)

test1-ruby: .FORCE
	rm -f test1-ruby/out.cup
	(cd ..; cabal run cat glue/ruby.skin glue/test1-ruby/ast.in) | awk '/grammar/ { p = 1; next; } /<<grammar/ { p = 0 } { if (p) print }' > test1-ruby/out.cup
	(cd test1-ruby; java -cp ../java_cup.jar java_cup.Main -nopositions -expect 1000 out.cup)
	(cd test1-ruby; ../make_lexer out.cup ../ruby.flex > out.flex)
	(cd test1-ruby; java -cp ../jflex.jar jflex.Main out.flex)
	(cd test1-ruby; javac -cp ../java_cup.jar:../jflex.jar:..:. Parser.java Lexer.java sym.java)
	(cd test1-ruby; javac -cp ../java_cup.jar:../jflex.jar:..:. Program.java TestJava.java)
	(cd test1-ruby; java -cp ../java_cup.jar:../jflex.jar:..:. TestJava test.ruby-skinned)

test2-java: .FORCE
	rm -f test2-java/out.cup
	(cd ..; cabal run cat glue/java.skin glue/test2-java/ast.in) | awk '/grammar/ { p = 1; next; } /<<grammar/ { p = 0 } { if (p) print }' > test2-java/out.cup
	(cd test2-java; java -cp ../java_cup.jar java_cup.Main -nopositions out.cup)
	(cd test2-java; ../make_lexer out.cup ../java.flex > out.flex)
	(cd test2-java; java -cp ../jflex.jar jflex.Main out.flex)
	(cd test2-java; javac -cp ../java_cup.jar:../jflex.jar:..:. Parser.java Lexer.java sym.java)
	(cd test2-java; javac -cp ../java_cup.jar:../jflex.jar:..:. Program.java TestJava.java)
	(cd test2-java; java -cp ../java_cup.jar:../jflex.jar:..:. TestJava test.java-skinned)

test2-ruby: .FORCE
	rm -f test2-ruby/out.cup
	(cd ..; cabal run cat glue/ruby.skin glue/test2-ruby/ast.in) | awk '/grammar/ { p = 1; next; } /<<grammar/ { p = 0 } { if (p) print }' > test2-ruby/out.cup
	(cd test2-ruby; java -cp ../java_cup.jar java_cup.Main -dump -nopositions -expect 1000 out.cup 2> out.dump)
	(cd test2-ruby; ../make_lexer out.cup ../ruby.flex > out.flex)
	(cd test2-ruby; java -cp ../jflex.jar jflex.Main out.flex)
	(cd test2-ruby; javac -cp ../java_cup.jar:../jflex.jar:..:. Parser.java Lexer.java sym.java)
	(cd test2-ruby; javac -cp ../java_cup.jar:../jflex.jar:..:. Program.java TestJava.java)
	(cd test2-ruby; java -cp ../java_cup.jar:../jflex.jar:..:. TestJava test1.ruby-skinned)
	(cd test2-ruby; java -cp ../java_cup.jar:../jflex.jar:..:. TestJava test2.ruby-skinned)


utils:
	javac skinner/lex/*.java skinner/util/*.java

.FORCE:
