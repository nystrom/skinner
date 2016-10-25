/*
 * This file is part of the Polyglot extensible compiler framework.
 *
 * Copyright (c) 2000-2006 Polyglot project group, Cornell University
 * 
 */

package skinner.lex;

import skinner.util.Position;

/** The base class of all tokens. */
public abstract class Token<T> {
  protected Position position;
  protected int symbol;

  public Token(Position position, int symbol)
  {
    this.position = position;
    this.symbol = symbol;
  }

  public Position getPosition()
  {
    return position;
  }

  public int symbol() {
      return symbol;
  }

  public abstract T getValue();

  protected static String escape(String s) {
    StringBuffer sb = new StringBuffer();
    for (int i=0; i<s.length(); i++)
      switch(s.charAt(i)) {
      case '\t': sb.append("\\t"); break;
      case '\f': sb.append("\\f"); break;
      case '\n': sb.append("\\n"); break;
      default:
	if ((int)s.charAt(i)<0x20 ||
              ((int)s.charAt(i) > 0x7e && (int)s.charAt(i) < 0xFF))
	  sb.append("\\"+Integer.toOctalString((int)s.charAt(i)));
	else
	  sb.append(s.charAt(i));
      }
    return sb.toString();
  }
}
