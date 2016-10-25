/*
 * Java 7 scanner for JFlex. 
 *
 * This file is part of the Polyglot extensible compiler framework.
 *
 * Copyright (c) 2000-2013 Polyglot project group, Cornell University
 * 
 */

import java.util.HashMap;
import java.math.BigInteger;
import skinner.lex.*;
import skinner.util.*;

@SuppressWarnings({"unused", "fallthrough", "all"})
%%

%public
%class Lexer
%type Token
%function nextToken

%unicode
%pack

%line
%column

%buffer 1048576

%state STRING, CHARACTER, TRADITIONAL_COMMENT, END_OF_LINE_COMMENT

%{
    StringBuffer sb = new StringBuffer();
    String file;
    String path;
    HashMap<String, Integer> keywords;
    Position commentBegin;

    public Lexer(java.io.Reader reader, String file, String path) {
        this(reader);
        this.file = file;
        this.path = path;
        this.keywords = new HashMap<>();
        init_keywords();
    }

    protected void init_keywords() {
    }

    public String file() {
        return file;
    }

    public String path() {
        return path;
    }

    private Position pos() {
        return new Position(path, file, yyline+1, yycolumn, yyline+1,
                            yycolumn + yytext().length());
    }

    private Position pos(int len) {
        return new Position(path, file, yyline+1, yycolumn-len-1, yyline+1,
                            yycolumn+1);
    }

    private Token key(int symbol) {
        return new Keyword(pos(), yytext(), symbol);
    }

    private Token op(int symbol) {
        return new Operator(pos(), yytext(), symbol);
    }

    private Token id() {
        return new Identifier(pos(), yytext(), sym.IDENTIFIER);
    }

    private String removeUnderscores(String s) {
        return s.replaceAll("_", "");
    }
    
    private Token int_lit(String s, int radix) {
        s = removeUnderscores(s);
        BigInteger x = new BigInteger(s, radix);
        boolean boundary = (radix == 10 && s.equals("2147483648"));
        int bits = radix == 10 ? 31 : 32;
        if (x.bitLength() > bits && ! boundary) {
            System.err.println(pos() + ": Integer literal \"" + yytext() + "\" out of range.");
        }
        return new IntegerLiteral(pos(), x.intValue(), sym.INT_LITERAL);
    }

    private Token long_lit(String s, int radix) {
        s = removeUnderscores(s);
        BigInteger x = new BigInteger(s, radix);
        boolean boundary = (radix == 10 && s.equals("9223372036854775808"));
        int bits = radix == 10 ? 63 : 64;
        if (x.bitLength() > bits && ! boundary) {
            System.err.println(pos() + ": Long literal \"" + yytext() + "\" out of range.");
            }
        return new LongLiteral(pos(), x.longValue(), sym.LONG_LITERAL);
            }

    private Token float_lit(String s) {
        try {
            s = removeUnderscores(s);
            Float x = Float.valueOf(s);
            boolean zero = true;
            for (int i = 0; i < s.length(); i++) {
                if ('1' <= s.charAt(i) && s.charAt(i) <= '9') {
                    zero = false;
                    break;
                }
                if (s.charAt(i) == 'e' || s.charAt(i) == 'E') {
                    break; // 0e19 is still 0
                }
            }
            if (x.isInfinite() || x.isNaN() || (x.floatValue() == 0 && ! zero)) {
                System.err.println(pos() + ": Illegal float literal \"" + yytext() + "\".");
            }
            return new FloatLiteral(pos(), x.floatValue(), sym.FLOAT_LITERAL);
        }
        catch (NumberFormatException e) {
            System.err.println(pos() + ": Illegal float literal \"" + yytext() + "\".");
            return new FloatLiteral(pos(), 0f, sym.FLOAT_LITERAL);
        }
    }

    private Token double_lit(String s) {
        try {
            s = removeUnderscores(s);
            Double x = Double.valueOf(s);
            boolean zero = true;
            for (int i = 0; i < s.length(); i++) {
                if ('1' <= s.charAt(i) && s.charAt(i) <= '9') {
                    zero = false;
                    break;
                }
                if (s.charAt(i) == 'e' || s.charAt(i) == 'E') {
                    break; // 0e19 is still 0
                }
            }
            if (x.isInfinite() || x.isNaN() || (x.doubleValue() == 0 && ! zero)) {
                System.err.println(pos() + ": Illegal double literal \"" + yytext() + "\".");
            }
            return new DoubleLiteral(pos(), x.doubleValue(), sym.DOUBLE_LITERAL);
        }
        catch (NumberFormatException e) {
            System.err.println(pos() + ": Illegal double literal \"" + yytext() + "\".");
            return new DoubleLiteral(pos(), 0., sym.DOUBLE_LITERAL);
        }
    }

    private Token char_lit(String s) {
        if (s.length() == 1) {
            char x = s.charAt(0);
            return new CharacterLiteral(pos(), x, sym.CHAR_LITERAL);
        }
        else {
            System.err.println(pos(s.length()) + ": Illegal character literal \'" + s + "\'");
            return new CharacterLiteral(pos(), '\0', sym.CHAR_LITERAL);
        }
    }

    private Token string_lit() {
        return new StringLiteral(pos(sb.length()), sb.toString(),
                                 sym.STRING_LITERAL);
    }

    private String chop(int i, int j) {
        return yytext().substring(i,yylength()-j);
    }

    private String chop(int j) {
        return chop(0, j);
    }

    private String chop() {
        return chop(0, 1);
    }
%}

%eofval{
    return new EOF(pos(), sym.EOF);
%eofval}

/* From Chapter 3 of the JLS: */

/* 3.4 Line Terminators */
/* LineTerminator:
      the ASCII LF character, also known as "newline"
      the ASCII CR character, also known as "return"
      the ASCII CR character followed by the ASCII LF character
*/
LineTerminator = \n|\r|\r\n

/* 3.6 White Space */
/*
WhiteSpace:
    the ASCII SP character, also known as "space"
    the ASCII HT character, also known as "horizontal tab"
    the ASCII FF character, also known as "form feed"
    LineTerminator
*/
WhiteSpace = [ \t\f] | {LineTerminator}

/* 3.8 Identifiers */
Identifier = [:jletter:] [:jletterdigit:]*

/* 3.10.1 Integer Literals */
DecimalNumeral = 0 | [1-9] {Digits}? | [1-9] [_]+ {Digits}
Digits = {Digit} | {Digit} {DigitAndUnderscore}* {Digit}
Digit = [0-9]
DigitAndUnderscore = {Digit} | "_"

HexNumeral = 0 [xX] {HexDigits}
HexDigits = {HexDigit} | {HexDigit} {HexDigitAndUnderscore}* {HexDigit}
HexDigit = [0-9a-fA-F]
HexDigitAndUnderscore = {HexDigit} | "_"

OctalNumeral = 0 [_]* {OctalDigits}
OctalDigits = {OctalDigit} | {OctalDigit} {OctalDigitAndUnderscore}* {OctalDigit}
OctalDigit = [0-7]
OctalDigitAndUnderscore = {OctalDigit} | "_"


BinaryNumeral = 0 [bB] {BinaryDigits}
BinaryDigits = {BinaryDigit} | {BinaryDigit} {BinaryDigitAndUnderscore}* {BinaryDigit}
BinaryDigit = [01]
BinaryDigitAndUnderscore = {BinaryDigit} | "_"


/* 3.10.2 Floating-Point Literals */
FloatingPointLiteral = {DecimalFloatingPointLiteral} | {HexadecimalFloatingPointLiteral}

DecimalFloatingPointLiteral = {Digits} "." {Digits}? {ExponentPart}? {FloatTypeSuffix}?
                     | "." {Digits} {ExponentPart}? {FloatTypeSuffix}?
                     | {Digits} {ExponentPart} {FloatTypeSuffix}?
                     | {Digits} {ExponentPart}? {FloatTypeSuffix}
                     
ExponentPart = [eE] {SignedInteger}
SignedInteger = [-+]? {Digits}

HexadecimalFloatingPointLiteral = {HexSignificand} {BinaryExponent} {FloatTypeSuffix}?
                     
HexSignificand = {HexNumeral} 
               | {HexNumeral} "." 
               | 0 [xX] {HexDigits}? "." {HexDigits}  

BinaryExponent = [pP] {SignedInteger}
FloatTypeSuffix = [fFdD]


/* 3.10.4 Character Literals */
OctalEscape = \\ [0-7]
            | \\ [0-7][0-7]
            | \\ [0-3][0-7][0-7]

%%

<YYINITIAL> {
    /* 3.7 Comments */
    "/*"    { yybegin(TRADITIONAL_COMMENT);
              commentBegin = pos(); }
    "//"    { yybegin(END_OF_LINE_COMMENT); }

    /* 3.10.4 Character Literals */
    \'      { yybegin(CHARACTER); sb.setLength(0); }

    /* 3.10.5 String Literals */
    \"      { yybegin(STRING); sb.setLength(0); }

    /* 3.9 Keywords */
    /* 3.8 Identifiers */
    {Identifier}   { Integer i = keywords.get(yytext());
                    if (i == null) return id();
                    else return key(i.intValue()); }

    /* 3.11 Separators */
    "("    { return op(sym.TOKEN_LPAREN);    }
    ")"    { return op(sym.TOKEN_RPAREN);    }
    "{"    { return op(sym.TOKEN_LBRACE);    }
    "}"    { return op(sym.TOKEN_RBRACE);    }
    "["    { return op(sym.TOKEN_LBRACK);    }
    "]"    { return op(sym.TOKEN_RBRACK);    }
    ";"    { return op(sym.TOKEN_SEMI); }
    ","    { return op(sym.TOKEN_COMMA);     }
    "."    { return op(sym.TOKEN_DOT);       }

    /* 3.12 Operators */
    "="    { return op(sym.TOKEN_EQ);         }
    ">"    { return op(sym.TOKEN_GT);         }
    "<"    { return op(sym.TOKEN_LT);         }
    "!"    { return op(sym.TOKEN_NOT);        }
    "~"    { return op(sym.TOKEN_TWIDDLE);       }
    "?"    { return op(sym.TOKEN_QUESTION);   }
    ":"    { return op(sym.TOKEN_COLON);      }
    "=="   { return op(sym.TOKEN_EQ_EQ);       }
    "<="   { return op(sym.TOKEN_LT_EQ);       }
    ">="   { return op(sym.TOKEN_GT_EQ);       }
    "!="   { return op(sym.TOKEN_BANG_EQ);      }
    "&&"   { return op(sym.TOKEN_AND_AND);     }
    "||"   { return op(sym.TOKEN_BAR_BAR);       }
    "++"   { return op(sym.TOKEN_PLUS_PLUS);   }
    "--"   { return op(sym.TOKEN_DASH_DASH); }
    "+"    { return op(sym.TOKEN_PLUS);       }
    "-"    { return op(sym.TOKEN_DASH);      }
    "*"    { return op(sym.TOKEN_STAR);       }
    "/"    { return op(sym.TOKEN_SLASH);        }
    "&"    { return op(sym.TOKEN_AND);        }
    "|"    { return op(sym.TOKEN_OR);         }
    "^"    { return op(sym.TOKEN_CARET);        }
    "%"    { return op(sym.TOKEN_PERCENT);        }
    "<<"   { return op(sym.TOKEN_LT_LT);     }
    ">>"   { return op(sym.TOKEN_GT_GT);     }
    ">>>"  { return op(sym.TOKEN_GT_GT_GT);    }
    "+="   { return op(sym.TOKEN_PLUS_EQ);     }
    "-="   { return op(sym.TOKEN_DASH_EQ);    }
    "*="   { return op(sym.TOKEN_STAR_EQ);     }
    "/="   { return op(sym.TOKEN_SLASH_EQ);      }
    "&="   { return op(sym.TOKEN_AND_EQ);      }
    "|="   { return op(sym.TOKEN_BAR_EQ);       }
    "^="   { return op(sym.TOKEN_CARET_EQ);      }
    "%="   { return op(sym.TOKEN_PERCENT_EQ);      }
    "<<="  { return op(sym.TOKEN_LT_LT_EQ);   }
    ">>="  { return op(sym.TOKEN_GT_GT_EQ);   }
    ">>>=" { return op(sym.TOKEN_GT_GT_GT_EQ);  }
    "@"    { return op(sym.TOKEN_AT);         }
    "..."    { return op(sym.TOKEN_DOT_DOT_DOT);         }

    /* 3.10.1 Integer Literals */
    {OctalNumeral} [lL]          { return long_lit(chop(), 8); }
    {HexNumeral} [lL]            { return long_lit(chop(2,1), 16); }
    {BinaryNumeral} [lL]        { return long_lit(chop(2,1), 2); }
    {DecimalNumeral} [lL]        { return long_lit(chop(), 10); }
    {OctalNumeral}               { return int_lit(yytext(), 8); }
    {HexNumeral}                 { return int_lit(chop(2,0), 16); }
    {BinaryNumeral}              { return int_lit(chop(2,0), 2); }
    {DecimalNumeral}             { return int_lit(yytext(), 10); }

    /* 3.10.2 Floating-Point Literals */
    {FloatingPointLiteral} [fF]  { return float_lit(chop()); }
    {DecimalNumeral} [fF]        { return float_lit(chop()); }
    {FloatingPointLiteral} [dD]  { return double_lit(chop()); }
    {DecimalNumeral} [dD]        { return double_lit(chop()); }
    {FloatingPointLiteral}       { return double_lit(yytext()); }

    /* 3.6 White Space */
    {WhiteSpace}                 { /* ignore */ }
}

<TRADITIONAL_COMMENT> {
    "*/"                         { yybegin(YYINITIAL); }
    <<EOF>>                      { yybegin(YYINITIAL);
                                   System.err.println(commentBegin + ": Unclosed comment"); }
    [^]                          { /* ignore */ }
}

<END_OF_LINE_COMMENT> {
    {LineTerminator}             { yybegin(YYINITIAL); }
    .                            { /* ignore */ }
}

<CHARACTER> {
    /* End of the character literal */
    \'                           { yybegin(YYINITIAL);
                                   return char_lit(sb.toString()); }

    /* 3.10.6 Escape Sequences for Character and String Literals */
    "\\b"                        { sb.append('\b'); }
    "\\t"                        { sb.append('\t'); }
    "\\n"                        { sb.append('\n'); }
    "\\f"                        { sb.append('\f'); }
    "\\r"                        { sb.append('\r'); }
    "\\\""                       { sb.append('\"'); }
    "\\'"                        { sb.append('\''); }
    "\\\\"                       { sb.append('\\'); }
    {OctalEscape}                { try {
                                       int x = Integer.parseInt(chop(1,0), 8);
                                       sb.append((char) x);
                                   }
                                   catch (NumberFormatException e) {
                                       System.err.println(pos() + ": Illegal octal escape \"" + yytext() + "\"");
                                   }
                                 }

    /* Illegal escape character */
    \\.                          { System.err.println(pos() + ": Illegal escape character \"" + yytext() + "\""); }

    /* Unclosed character literal */
    {LineTerminator}             { yybegin(YYINITIAL);
                                   System.err.println(pos(sb.length()) + ": Unclosed character literal"); }

    /* Anything else is okay */
    [^\r\n\'\\]+                 { sb.append( yytext() ); }
}

<STRING> {
    /* End of string */
    \"                           { yybegin(YYINITIAL);
                                   return string_lit(); }

    /* 3.10.6 Escape Sequences for Character and String Literals */
    "\\b"                        { sb.append( '\b' ); }
    "\\t"                        { sb.append( '\t' ); }
    "\\n"                        { sb.append( '\n' ); }
    "\\f"                        { sb.append( '\f' ); }
    "\\r"                        { sb.append( '\r' ); }
    "\\\""                       { sb.append( '\"' ); }
    "\\'"                        { sb.append( '\'' ); }
    "\\\\"                       { sb.append( '\\' ); }
    {OctalEscape}                { try {
                                       int x = Integer.parseInt(chop(1,0), 8);
                                       sb.append((char) x);
                                   }
                                   catch (NumberFormatException e) {
                                       System.err.println(pos() + ": Illegal octal escape \"" + yytext() + "\"");
                                   }
                                 }

    /* Illegal escape character */
    \\.                          { System.err.println(pos() + ": Illegal escape character \"" + yytext() + "\""); }

    /* Unclosed string literal */
    {LineTerminator}             { yybegin(YYINITIAL);
                                   System.err.println(pos(sb.length()) + ": Unclosed string literal"); }

    /* Anything else is okay */
    [^\r\n\"\\]+                 { sb.append( yytext() ); }
}

/* Fallthrough case: anything not matched above is an error */
[^]                              { System.err.println(pos() + ": Illegal character \"" + yytext() + "\""); }
