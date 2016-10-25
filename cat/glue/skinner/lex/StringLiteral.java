/*
 * This file is part of the Polyglot extensible compiler framework.
 *
 * Copyright (c) 2000-2006 Polyglot project group, Cornell University
 * 
 */

package skinner.lex;

import java_cup.runtime.Symbol;
import skinner.util.Position;

/** A token class for string literals. */
public class StringLiteral extends Token<String> {
  protected String val;
  public StringLiteral(Position position, String s, int sym) {
      super(position, sym);
      this.val = s;
  }

  public String getValue() { return val; }

  public String toString() {
    return "string literal \""+Token.escape(val)+"\"";
  }
}
