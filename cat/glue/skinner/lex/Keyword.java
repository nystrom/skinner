/*
 * This file is part of the Polyglot extensible compiler framework.
 *
 * Copyright (c) 2000-2006 Polyglot project group, Cornell University
 * 
 */

package skinner.lex;

import java_cup.runtime.Symbol;
import skinner.util.Position;

/** A token class for keywords. */
public class Keyword extends Token<String> {
    protected String keyword;

  public Keyword(Position position, String s, int sym) {
      super(position, sym);
      keyword = s;
  }

  public String toString() {
      return keyword;
  }

  public String getValue() {
    return keyword;
  }
}
