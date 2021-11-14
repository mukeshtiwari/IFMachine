package secc.c;

import java.util.Set;
import beaver.Symbol;
import secc.c.Parser.Terminals;

%%

%public
%class Scanner
%extends beaver.Scanner
%function nextToken
%type Symbol
%yylexthrow Scanner.Exception

%eofval{
	return newToken(Terminals.EOF);
%eofval}

%line
%column

%{
    public Set<String> types;
    public Set<String> preds;
    
    Symbol string(String name) {
    	return newToken(Terminals.STRING, name.substring(1, name.length() - 1));
    }

    Symbol resolve(String name) {
    	if(types.contains(name)) {
    		return newToken(Terminals.TYPE, name);
    	} else if (preds.contains(name)) {
    		return newToken(Terminals.PRED, name);
    	} else {
    		return newToken(Terminals.ID,   name);
    	}
    }

	Symbol newToken(short id)
	{
		return newToken(id, yytext());
	}

	Symbol newToken(short id, Object value)
	{
		return new Symbol(id, yyline + 1, yycolumn + 1, yylength(), value);
	}
%}

NL = \r|\n|\r\n
WS = {NL} | [ \t\f]

%%

<YYINITIAL> {

"//" .* {NL} {}
"#"  .* {NL} {}
"/*" [^*] ~"*/" | "/*" "*"+ "/" {}
{WS}+ {}


"("         { return newToken(Terminals.LPAREN);   }
")"         { return newToken(Terminals.RPAREN);   }
"["         { return newToken(Terminals.LBRACK);   }
"]"         { return newToken(Terminals.RBRACK);   }
"{"         { return newToken(Terminals.LBRACE);   }
"}"         { return newToken(Terminals.RBRACE);   }
"++"        { return newToken(Terminals.INCR);     }
"--"        { return newToken(Terminals.DECR);     }
"."         { return newToken(Terminals.DOT);      }
"->"        { return newToken(Terminals.ARROW);    }
"!"         { return newToken(Terminals.BANG);     }
"~"         { return newToken(Terminals.TILDE);    }
"sizeof"    { return newToken(Terminals.SIZEOF);   }
"*"         { return newToken(Terminals.STAR);     }
"/"         { return newToken(Terminals.DIV);      }
"%"         { return newToken(Terminals.MOD);      }
"+"         { return newToken(Terminals.PLUS);     }
"-"         { return newToken(Terminals.MINUS);    }
"<<"        { return newToken(Terminals.SHL);      }
">>"        { return newToken(Terminals.SHR);      }
"<"         { return newToken(Terminals.LT);       }
"<="        { return newToken(Terminals.LE);       }
">="        { return newToken(Terminals.GE);       }
">"         { return newToken(Terminals.GT);       }
"=="        { return newToken(Terminals.EQ);       }
"!="        { return newToken(Terminals.NEQ);      }
"&"         { return newToken(Terminals.AMP);      }
"^"         { return newToken(Terminals.CARET);    }
"|"         { return newToken(Terminals.PIPE);     }
"&&"        { return newToken(Terminals.AND);      }
"||"        { return newToken(Terminals.OR);       }
"?"         { return newToken(Terminals.QUESTION); }
":"         { return newToken(Terminals.COLON);    }
":="        { return newToken(Terminals.COLONEQ);  }
"="         { return newToken(Terminals.ASG); }
"+="|"-="|"*="|"/="|"%="|"<<="|">>="|"&="|"^="|"|="
            { return newToken(Terminals.ASG_OP, yytext()); }
","         { return newToken(Terminals.COMMA);    }
";"         { return newToken(Terminals.SEMICOLON);}

"void"      { return newToken(Terminals.VOID);     }
"char"      { return newToken(Terminals.CHAR);     }
// "short"     { return newToken(Terminals.SHORT);    }
"int"       { return newToken(Terminals.INT);      }
// "long"      { return newToken(Terminals.LONG);     }
// "signed"    { return newToken(Terminals.SIGNED);   }
// "unsigned"  { return newToken(Terminals.UNSIGNED); }

"struct"    { return newToken(Terminals.STRUCT);   }
"union"     { return newToken(Terminals.UNION);    }
"enum"      { return newToken(Terminals.ENUM);     }
"typedef"   { return newToken(Terminals.TYPEDEF);  }

"list<"      { return newToken(Terminals.LIST_LT);     }
"map<"       { return newToken(Terminals.MAP_LT);      }

"break"     { return newToken(Terminals.BREAK);    }
"return"    { return newToken(Terminals.RETURN);   }
"continue"  { return newToken(Terminals.CONTINUE); }
"do"        { return newToken(Terminals.DO);       }
"while"     { return newToken(Terminals.WHILE);    }
"for"       { return newToken(Terminals.FOR);      }
"if"        { return newToken(Terminals.IF);       }
"else"      { return newToken(Terminals.ELSE);     }

"_"         { return newToken(Terminals.UNDERSCORE); }
"requires"  { return newToken(Terminals.REQUIRES); }
"ensures"   { return newToken(Terminals.ENSURES);  }
"invariant" { return newToken(Terminals.INVARIANT);}
"resource"  { return newToken(Terminals.RESOURCE); }
"maintains" { return newToken(Terminals.MAINTAINS);}
"fails"     { return newToken(Terminals.FAILS);    }
"lemma"     { return newToken(Terminals.LEMMA);    }
"induct"    { return newToken(Terminals.INDUCT);   }
"pure"      { return newToken(Terminals.PURE);     }
"prune"     { return newToken(Terminals.PRUNE);    }
"shared"    { return newToken(Terminals.SHARED);   }
"atomic"    { return newToken(Terminals.ATOMIC);   }
"rely"      { return newToken(Terminals.RELY);     }
"guarantee" { return newToken(Terminals.GUARANTEE); }
"begin"     { return newToken(Terminals.BEGIN);    }
"end"       { return newToken(Terminals.END);      }

"predicate" { return newToken(Terminals.PREDICATE);}
"constant"  { return newToken(Terminals.CONSTANT); }
"function"  { return newToken(Terminals.FUNCTION); }
"assume"    { return newToken(Terminals.ASSUME);   }
"assert"    { return newToken(Terminals.ASSERT);   }
"unfold"    { return newToken(Terminals.UNFOLD);   }
"fold"      { return newToken(Terminals.FOLD);     }
"apply"     { return newToken(Terminals.APPLY);    }
"rewrites"  { return newToken(Terminals.REWRITES); }
"axioms"    { return newToken(Terminals.AXIOMS);   }
// "then"      { return newToken(Terminals.THEN);     }

"==>"       { return newToken(Terminals.IMP);      }
"<=>"       { return newToken(Terminals.EQV);      }
"::"        { return newToken(Terminals.DCOLON);   }
","         { return newToken(Terminals.COMMA);    }
";"         { return newToken(Terminals.SEMICOLON);}
"|->"       { return newToken(Terminals.PTO);      }

"exists"    { return newToken(Terminals.EXISTS);   }
"forall"    { return newToken(Terminals.FORALL);   }
"old"       { return newToken(Terminals.OLD);      }

\"(\\.|[^\"\\])*\"
            { return string(yytext()); }

"$" [a-zA-Z_][a-zA-Z_0-9]*
            { return newToken(Terminals.PARAM, yytext().substring(1)); }
            
[a-zA-Z_][a-zA-Z_0-9]*
            { return resolve(yytext()); }

[0-9]+      { return newToken(Terminals.NUM, new Integer(yytext())); }

[^]         { throw new Scanner.Exception("unexpected character '" + yytext() + "'"); }

}

