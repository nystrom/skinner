/*
 * This file is part of the Polyglot extensible compiler framework.
 *
 * Copyright (c) 2000-2006 Polyglot project group, Cornell University
 * 
 */

package skinner.lex;

import skinner.util.Position;

/** A token class for int literals. */
public class IntegerLiteral extends Token<Integer> {
  protected int val;
  public IntegerLiteral(Position position, int i, int sym) {
      super(position, sym);
      this.val = i;
  }
  public Integer getValue() {
    return val;
  }
  public String toString() { return "integer " + val; }
}
