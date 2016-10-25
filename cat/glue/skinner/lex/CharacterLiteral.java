/*
 * This file is part of the Polyglot extensible compiler framework.
 *
 * Copyright (c) 2000-2006 Polyglot project group, Cornell University
 * 
 */

package skinner.lex;

import skinner.util.Position;

/** Token class for char literals. */
public class CharacterLiteral extends Token<Character> {
  protected char val;

  public CharacterLiteral(Position position, char c, int sym)
  {
    super(position, sym); 
    this.val = c; 
  }
  
  public Character getValue() 
  {
    return val;
  }

  public String getEscapedValue()
  {
    return Token.escape( String.valueOf( val));
  }

  public String toString() 
  {
    return "char literal '" + getEscapedValue() + "'";
  }
}
