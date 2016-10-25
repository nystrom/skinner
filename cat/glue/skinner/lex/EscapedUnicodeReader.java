/*
 * This file is part of the Polyglot extensible compiler framework.
 *
 * Copyright (c) 2000-2006 Polyglot project group, Cornell University
 * 
 * Taken from the CUP website from the handwritten Lexer by Scott Ananian 
 * <cananian@alumni.princeton.edu>.
 */

package skinner.lex;

import java.io.Reader;
import java.io.FilterReader;
import java.io.IOException;

/** A reader that translates escaped unicode into unicode characters. */
public class EscapedUnicodeReader extends FilterReader {

  int pushback=-1;
  boolean isEvenSlash = true;

  public EscapedUnicodeReader(Reader in) {
    super(in);
  }
  public Reader getSource() {
    return in;
  }
  public int read() throws IOException {
    int r = (pushback==-1)?in.read():pushback; pushback=-1;
    
    if (r!='\\') {
      isEvenSlash=true;
      return r;
    } else { // found a backslash;
      if (!isEvenSlash) { // Only even slashes are eligible unicode escapes.
	isEvenSlash=true;
	return r;
      }
      
      // Check for the trailing u.
      pushback=in.read();
      if (pushback!='u') {
	isEvenSlash=false;
	return '\\';
      }

      // OK, we've found backslash-u.  
      // Reset pushback and snarf up all trailing u's.
      pushback=-1;
      while((r=in.read())=='u')
	;
      // Now we should find 4 hex digits. 
      // If we don't, we can raise bloody hell.
      int val=0;
      for (int i=0; i<4; i++, r=in.read()) {
	int d=Character.digit((char)r, 16);
	if (r<0 || d<0) {
            // invalid unicode character. Spend some time getting a 
            // meaningful error message
            String code = "";
            for (int j = 0; j < i; j++) {
                code = Character.forDigit(val % 16, 16) + code;
                val = val/16;
            }
            for (; i<4; i++, r=in.read()) {
                code += ((char)r);
            }
            
	    throw new IOException("Invalid unicode escape character: \\u" + code);
        }
	val = (val*16) + d;
      }
      // yeah, we made it.
      pushback = r;
      isEvenSlash=true;
      return val;
    }
  }
  // synthesize array read from single-character read.
  public int read(char cbuf[], int off, int len) throws IOException {
    for (int i=0; i<len; i++) {
      int c = read();
      if (c==-1) return (i==0)?-1:i; // end of stream reached.
      else cbuf[i+off] = (char) c;
    }
    return len;
  }

  public boolean markSupported() { return false; }

  public boolean ready() throws IOException {
    if (pushback!=-1) return true;
    else return in.ready();
  }
}
