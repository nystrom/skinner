/*
 * This file is part of the Polyglot extensible compiler framework.
 *
 * Copyright (c) 2000-2006 Polyglot project group, Cornell University
 * 
 */

package skinner.lex;

import skinner.util.Position;

/** A token class for long literals. */
public class LongLiteral extends Token<Long> {
  protected long val;
  public LongLiteral(Position position, long l, int sym) {
      super(position, sym);
      this.val = l;
  }
  public Long getValue() {
    return val;
  }
}
