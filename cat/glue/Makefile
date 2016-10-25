.SUFFIXES: .java .class .cup .flex

all:
	# rm -f out.cup
	make out.cup
	make Parser.java
	make Lexer.java
	make Parser.class
	make Lexer.class
	make TestJava.class

out.cup:
	(cd ..; make java) | awk '/grammar/ { p = 1; next; } /<<grammar/ { p = 0 } { if (p) print }' > out.cup

Parser.class: Parser.java
	javac -cp java_cup.jar:jflex.jar:. Parser.java

Parser.java: out.cup
	java -cp java_cup.jar java_cup.Main -nopositions out.cup

out.flex: java.flex make_lexer out.cup
	./make_lexer > out.flex

Lexer.java: out.flex
	java -cp jflex.jar jflex.Main out.flex

Lexer.class: Lexer.java
	javac -cp jflex.jar:. Lexer.java

skinner/lex/Token.class:
	javac -cp java_cup.jar:. skinner/lex/*.java

.class.java:
	javac -cp java_cup.jar:jflex.jar:. $<

.FORCE:

slowtest:
	rm -f out.cup
	make all

test:
	java -cp java_cup.jar:jflex.jar:. TestJava foo.java
