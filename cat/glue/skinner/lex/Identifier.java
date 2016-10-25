/*
 * This file is part of the Polyglot extensible compiler framework.
 *
 * Copyright (c) 2000-2006 Polyglot project group, Cornell University
 * 
 */

package skinner.lex;

import java_cup.runtime.Symbol;
import skinner.util.Position;

/** A token class for identifiers. */
public class Identifier extends Token<String> {
  protected String identifier;

  public Identifier(Position position, String identifier, int sym)
  {
	super(position, sym);
	this.identifier=identifier;
  }

  public String getIdentifier() { return identifier; }
  public String getValue() { return identifier; }

  public String toString() { return "identifier \"" + identifier + "\""; }
}
