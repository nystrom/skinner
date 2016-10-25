import java_cup.runtime.*;
import java.io.*;
import skinner.lex.*;

public class TestJava {
  public static void main(String[] args) throws IOException {
    if (args.length != 1) {
      System.err.println("usage: java TestJava foo.java");
      System.exit(1);
    }

    String file = args[0];
    FileReader fr = new FileReader(file);
    Reader r = new EscapedUnicodeReader(new FileReader(file));
    Lexer l = new Lexer(r, file, file);
    Parser p = new Parser(l);

    // Get the AST
    Program t = parse(p, file);
    System.out.println(t);
  }

  static Program parse(Parser p, String file) {
    try {
      java_cup.runtime.Symbol sym = p.parse();

      if (sym != null && sym.value instanceof Program) {
	Program t = (Program) sym.value;
	return t;
      }
    }
    catch (IOException e) {
      System.err.println(e.getMessage());
      return null;
    }
    catch (RuntimeException e) {
      // Let the Compiler catch and report it.
      throw e;
    }
    catch (Exception e) {
      // Used by cup to indicate a non-recoverable error.
      if (e.getMessage() != null) {
	System.err.println(e.getMessage());
	return null;
      }
    }

    System.err.println("Unable to parse " + file + ".");

    return null;
  }
}

