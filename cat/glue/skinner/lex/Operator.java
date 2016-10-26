/*
 * This file is part of the Polyglot extensible compiler framework.
 *
 * Copyright (c) 2000-2006 Polyglot project group, Cornell University
 * 
 */

package skinner.lex;

import java.util.Hashtable;
import skinner.util.Position;
import java_cup.runtime.Symbol;

/** A token class for operators. */
public class Operator extends Token<String> {
    protected String which;
  public Operator(Position position, String which, int sym) {
      super(position, sym);
      this.which = which;
  }

  public String toString() { return "operator '" + escape(which) + "' (" + symbol() + ")"; }

  public String getValue() { return which; }
}
