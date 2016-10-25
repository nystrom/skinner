/*
 * This file is part of the Polyglot extensible compiler framework.
 *
 * Copyright (c) 2000-2006 Polyglot project group, Cornell University
 * 
 */

package skinner.lex;

import java_cup.runtime.Symbol;
import skinner.util.Position;

/** Token class for end-of-file. */
public class EOF extends Token<String> {
  public EOF(Position position, int sym) { super(position, sym); }
  public String toString() { return "end of file"; }
  public String getValue() { return ""; }
}
