/*
 * This file is part of the Polyglot extensible compiler framework.
 *
 * Copyright (c) 2000-2006 Polyglot project group, Cornell University
 * 
 */

package skinner.lex;

import java_cup.runtime.Symbol;
import skinner.util.Position;

/** A token class for float literals. */
public class FloatLiteral extends Token<Float> {
  protected float val;

  public FloatLiteral(Position position, float f, int sym) {
      super(position, sym);
      this.val = f;
  }

  public Float getValue() {
    return val;
  }
}
