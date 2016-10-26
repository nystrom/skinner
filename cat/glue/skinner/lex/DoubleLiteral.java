/*
 * This file is part of the Polyglot extensible compiler framework.
 *
 * Copyright (c) 2000-2006 Polyglot project group, Cornell University
 * 
 */

package skinner.lex;

import java_cup.runtime.Symbol;
import skinner.util.Position;

/** Token class for double literals. */
public class DoubleLiteral extends Token<Double> {
  protected double val;

  public DoubleLiteral(Position position, double d, int sym) {
      super(position, sym);
      this.val = d;
  }

  public Double getValue() {
    return val;
  }
  public String toString() { return "double " + val; }
}
