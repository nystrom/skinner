/*
 * Ruby scanner for JFlex. 
 * Based on the Polyglot Java scanner.
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

%state REGEXP, STRING, STRING2, END_OF_LINE_COMMENT, NEWLINE

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

    private Token regexp_lit() {
        return new StringLiteral(pos(sb.length()), sb.toString(),
                                 sym.REGEXP_LITERAL);
    }

    private Token string_lit() {
        return new StringLiteral(pos(sb.length()), sb.toString(),
                                 sym.STRING_LITERAL);
    }

    private Token terminator() {
        return new Operator(pos(), ";", sym.TOKEN_SEMI);
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
WhiteSpace = [ \t\f]

/* 3.8 Identifiers */
Identifier = [$@]? [a-zA-Z] [a-zA-Z0-9]* [!?]?

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
    "#"     { yybegin(END_OF_LINE_COMMENT); }

    /* 3.10.4 String Literals */
    \'      { yybegin(STRING2); sb.setLength(0); }

    /* 3.10.5 String Literals */
    \"      { yybegin(STRING); sb.setLength(0); }

    /* HACK HACK HACK
     * If we see a /, check if there is another / before the end of the line.
     * If so, scan as a regexp, otherwise, scan as a / token.
     */

    /* FIXME */
    "/"              { return op(sym.TOKEN_SLASH); }

    /*
    "/" / "/[^/]*$"  { return op(sym.TOKEN_SLASH); }
    "/"        { yybegin(REGEXP); sb.setLength(0); }
    */

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
    "::"    { return op(sym.TOKEN_COLON_COLON);      }
    "=="   { return op(sym.TOKEN_EQ_EQ);       }
    "==="  { return op(sym.TOKEN_EQ_EQ_EQ);       }
    "=~"   { return op(sym.TOKEN_EQ_TWIDDLE);       }
    "!~"   { return op(sym.TOKEN_BANG_TWIDDLE);       }
    "**"   { return op(sym.TOKEN_STAR_STAR);       }
    "**="   { return op(sym.TOKEN_STAR_STAR_EQ);       }
    "[]"   { return op(sym.TOKEN_LBRACK_RBRACK);       }
    "[]="   { return op(sym.TOKEN_LBRACK_RBRACK_EQ);       }
    "+@"   { return op(sym.TOKEN_PLUS_AT);       }
    "-@"   { return op(sym.TOKEN_DASH_AT);       }
    ".."   { return op(sym.TOKEN_DOT_DOT);       }
    "..."   { return op(sym.TOKEN_DOT_DOT_DOT);       }
    "<="   { return op(sym.TOKEN_LT_EQ);       }
    ">="   { return op(sym.TOKEN_GT_EQ);       }
    "!="   { return op(sym.TOKEN_BANG_EQ);      }
    "&&"   { return op(sym.TOKEN_AND_AND);     }
    "||"   { return op(sym.TOKEN_BAR_BAR);       }
    "++"   { return op(sym.TOKEN_PLUS_PLUS);   }
    "--"   { return op(sym.TOKEN_DASH_DASH); }
    "<<"   { return op(sym.TOKEN_LT_LT);      }
    ">>"   { return op(sym.TOKEN_GT_GT);      }
    "+"    { return op(sym.TOKEN_PLUS);       }
    "-"    { return op(sym.TOKEN_DASH);      }
    "*"    { return op(sym.TOKEN_STAR);       }
    "/"    { return op(sym.TOKEN_SLASH);        }
    "&"    { return op(sym.TOKEN_AND);        }
    "|"    { return op(sym.TOKEN_OR);         }
    "^"    { return op(sym.TOKEN_CARET);        }
    "%"    { return op(sym.TOKEN_PERCENT);        }
    "<=>"  { return op(sym.TOKEN_LT_EQ_GT);    }
    "+="   { return op(sym.TOKEN_PLUS_EQ);     }
    "-="   { return op(sym.TOKEN_DASH_EQ);    }
    "*="   { return op(sym.TOKEN_STAR_EQ);     }
    "/="   { return op(sym.TOKEN_SLASH_EQ);      }
    "&="   { return op(sym.TOKEN_AND_EQ);      }
    "|="   { return op(sym.TOKEN_BAR_EQ);       }
    "^="   { return op(sym.TOKEN_CARET_EQ);      }
    "%="   { return op(sym.TOKEN_PERCENT_EQ);      }
    "<<="   { return op(sym.TOKEN_LT_LT_EQ);      }
    ">>="   { return op(sym.TOKEN_GT_GT_EQ);      }
    "@"    { return op(sym.TOKEN_AT);         }
    "=>"    { return op(sym.TOKEN_EQ_GT);         }

    /* 3.10.1 Integer Literals */
    {OctalNumeral}               { return int_lit(yytext(), 8); }
    {HexNumeral}                 { return int_lit(chop(2,0), 16); }
    {BinaryNumeral}              { return int_lit(chop(2,0), 2); }
    {DecimalNumeral}             { return int_lit(yytext(), 10); }

    /* 3.10.2 Floating-Point Literals */
    {FloatingPointLiteral}       { return double_lit(yytext()); }

    /* 3.6 White Space */
    {WhiteSpace}                 { /* ignore */ }

    /* Newlines are virtual semicolons */
    {LineTerminator}             { yybegin(NEWLINE); }
    ";"                          { yybegin(NEWLINE); }
}

/* match newlines, ignoring spaces, returning a ; token at the end. */
<NEWLINE> {
    {WhiteSpace}                 { /* ignore */ }
    {LineTerminator}             { /* ignore */ }
    ";"                          { /* ignore */ }
    "#"                          { yybegin(END_OF_LINE_COMMENT); }
    <<EOF>>                      { yybegin(YYINITIAL); }
    .                            { yybegin(YYINITIAL);
                                   yypushback(1);
                                   return terminator(); }
}

<END_OF_LINE_COMMENT> {
    {LineTerminator}             { yybegin(NEWLINE); }
    .                            { /* ignore */ }
}

<REGEXP> {
    "/"                          { yybegin(YYINITIAL);
                                   return regexp_lit(); }

    {LineTerminator}             { yybegin(YYINITIAL);
                                   System.err.println(pos(sb.length()) + ": Unclosed regexp literal"); }

    [^\r\n/]+                    { sb.append(yytext() ); }
}

<STRING2> {
    /* End of the string literal */
    \'                           { yybegin(YYINITIAL);
                                   return string_lit(); }

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

    /* Unclosed string literal */
    {LineTerminator}             { yybegin(YYINITIAL);
                                   System.err.println(pos(sb.length()) + ": Unclosed string literal"); }

    /* Anything else is okay */
    [^\r\n\'\\]+                 { sb.append(yytext() ); }
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
    [^\r\n\"\\]+                 { sb.append(yytext() ); }
}

/* Fallthrough case: anything not matched above is an error */
[^]                              { System.err.println(pos() + ": Illegal character \"" + yytext() + "\""); }
