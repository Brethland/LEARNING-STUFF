// A toy Scheme Interpreter.
// By Brethland, for Yuki.
/* TODO : 1. Garbage Collection
          2. Error Handling
          3. Real Number
          4. Type Checker
          5. Continuation
*/
#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include <stdint.h>
#include <string.h>
#include <assert.h>

// Types and Keywords
typedef enum {
    SCM_CELL, SCM_NUMBER, SCM_STRING, SCM_BOOL, SCM_CONTEXT, SCM_FUNCTION, SCM_BUILTIN, SCM_SYMBOL 
} ScmValueType;

typedef enum {
    T_LPAREN, T_RPAREN, T_SYMBOL, T_QUOTE, T_ERROR, T_EOF, T_PERIOD
} SExprToken;

enum {
    KWD_IF, KWD_QUOTE, KWD_LAMBDA, KWD_LET, KWD_DEFINE, KWD_BEGIN, NUM_KEYWORDS
};

static const char *keyword_names[] = {
	"if", "quote", "lambda", "let", "define", "begin"
};

typedef struct _ScmValue *(*ScmBuiltin)(struct _ScmValue *args);

typedef struct _ScmValue {
    unsigned int type   : 31;
    union {
        unsigned int i;
        char *s;
        struct {
            struct _ScmValue *car, *cdr;
        } cell;
        struct _ScmValue *symname;
        struct {
      struct _ScmValue *parent, *vars;
    } context;
    struct {
      struct _ScmValue *context, *code;
    } func;
    ScmBuiltin builtin;
    } v;
} ScmValue;
#define CAR(val) ((val)->v.cell.car)
#define CDR(val) ((val)->v.cell.cdr)

typedef struct {
    char *buf;
    unsigned int pos;
    ScmValue *value;
} ScmLexer;

static ScmValue *values = NULL;
static ScmValue *keywords[NUM_KEYWORDS];
static ScmValue **symbols = NULL;
static unsigned int numSymbols = 0;
static ScmValue *globalContext;
static ScmValue deferredCall;

//Initialize New Values
static ScmValue *newValue(ScmValueType type)
{
    ScmValue *res = calloc(1, sizeof(ScmValue));
    res->type = type;
    return res;
}

static ScmValue *newNumber(ScmValueType type, unsigned int val) {
    ScmValue *res = newValue(type);
    res->v.i = val;
    return res;
}

static ScmValue *newCons(ScmValue *car, ScmValue *cdr) {
    ScmValue *res = newValue(SCM_CELL);
    CAR(res) = car, CDR(res) = cdr;
    return res;
}

static ScmValue *newString(const char *data, size_t len) {
    char *s = malloc(len + 1);
    memcpy(s, data, len); s[len] = '\0';
    ScmValue *res = newValue(SCM_STRING);
    res->v.s = s;
    return res;
}

ScmValue *findSymbol(const char *name, size_t len) {
    ScmValue *res, *symname;
    int i;
    for(i = 0; i < numSymbols; i++) {
        symname = symbols[i]->v.symname;
        if (strlen(symname->v.s) == len && !memcmp(symname->v.s, name, len)) return symbols[i];
    }
    res = newValue(SCM_SYMBOL);
    res->v.symname = newString(name, len);
    symbols = realloc(symbols, sizeof(*symbols) * (numSymbols + 1));
    return symbols[numSymbols++] = res;
}

// Transform some basic procedures into C functions
static void printList(ScmValue *value, char *deliminator);

void innerPrint(ScmValue *val) {
    if(val == NULL) printf("()");
    else {
        switch(val->type) {
            case SCM_NUMBER :
              printf("%d", val->v.i); break;
            case SCM_STRING :
              printf("\"%s\"", val->v.s); break;
            case SCM_BOOL :
              printf("#%c", val->v.i ? 't' : 'f'); break;
            case SCM_CELL :
              printList(val, ""); break;
            case SCM_CONTEXT :
              printf("<context>"); break;
            case SCM_FUNCTION :
              printList(val->v.func.code, "lambda "); break;
            case SCM_SYMBOL :
              printf("%s", val->v.symname->v.s); break;
            case SCM_BUILTIN :
              printf("<builtin procedure>"); break;
        }
    }
}

static void printList(ScmValue *val, char *deliminator) {
    printf("(%s", deliminator);
    while (val != NULL) {
        if (val->type != SCM_CELL) {
            printf(". ");
            innerPrint(val);
            break;
        }
        innerPrint(CAR(val));
        val = CDR(val);
        if (val != NULL) {
            printf(" ");
        }
    }
    printf(")");
}

static int innerEqual(ScmValue *v1, ScmValue *v2) {
    if(v1 == NULL || v2 == NULL) return v1 == v2;
    if(v1->type != v2->type) return 0;
    switch(v1->type) {
        case SCM_STRING :
          return !strcmp(v1->v.s, v2->v.s);
        case SCM_NUMBER :
        case SCM_BOOL : return v1->v.i == v2->v.i;
        default : return v1 == v2;
    }
}

static int innerLt(ScmValue *v1, ScmValue *v2) {
    if(v1 == NULL || v2 == NULL || v1->type != v2->type) return 0;
    switch (v1->type) {
        case SCM_STRING: 
          return strcmp(v1->v.s, v2->v.s) < 0; 
        case SCM_NUMBER :
        case SCM_BOOL : return v1->v.i < v2->v.i;
        default : return 0;
    }
}

// Lexer
static int isSymChar(char c) { return !isspace(c) && strchr("()[]{}\",'`;#|\\", c) == NULL; }

void initLexer(ScmLexer *lexer, char *buf) { lexer->buf = buf, lexer->pos = 0; }

#define chr lexer->buf[lexer->pos]

static SExprToken readString(ScmLexer *lexer) {
    int s = lexer->pos;
    while(chr != '\0' && chr != '"') lexer->pos++;
    if(chr == '\0') return T_ERROR;
    lexer->value = newString(lexer->buf + s, lexer->pos - s); lexer->pos++;
    return T_SYMBOL;
}

SExprToken readToken(ScmLexer *lexer) {
    while(chr != '\0') {
        if(chr == ';') {
            do {
				lexer->pos++;
				if (chr == '\0') return T_ERROR;
			} while (chr != '\n');
        } else if(!isspace(chr)) break;
        lexer->pos++;
    }
    if(chr == '\0') return T_EOF;
    switch (lexer->buf[lexer->pos++]) {
		case '.': return T_PERIOD;
		case '(': return T_LPAREN;
		case ')': return T_RPAREN;
		case '\'': return T_QUOTE;
		case '#':
			lexer->value = newNumber(SCM_BOOL, chr == 't');
			if (chr != 't' && chr != 'f') return T_ERROR;
			lexer->pos++;
			return T_SYMBOL;
		case '"': return readString(lexer);
		default: lexer->pos--; break;
	}
    if(isdigit(chr)) {
		lexer->value = newValue(SCM_NUMBER);
		lexer->value->v.i = 0;
		while (chr != '\0' && isdigit(chr)) {
			lexer->value->v.i = lexer->value->v.i * 10 + (chr - '0');
			lexer->pos++;
		}
		return T_SYMBOL;
	} else if (isSymChar(chr)) {
		int s = lexer->pos;
		while (chr != '\0' && isSymChar(chr)) lexer->pos++;
		lexer->value = findSymbol(lexer->buf + s, lexer->pos - s);
		return T_SYMBOL;
	} else return T_ERROR;
}

#undef chr

// Parser
static ScmValue *parseToken(ScmLexer *lexer, SExprToken token);

static ScmValue *parseList(ScmLexer *lexer) {
    ScmValue *res, **rover=&res;
	while(1) {
		SExprToken token = readToken(lexer);
		if (token == T_EOF || token == T_ERROR) return NULL;
		if (token == T_RPAREN) break;
        if (token == T_PERIOD) {
			token = readToken(lexer);
			*rover = parseToken(lexer, token);
			token = readToken(lexer);
			if (token != T_RPAREN) return NULL;
			return res;
		}
		*rover = newValue(SCM_CELL);
		CAR(*rover) = parseToken(lexer, token);
		rover = &CDR(*rover);
	}
	*rover = NULL;
	return res;
}

static ScmValue *parseQuoted(ScmLexer *lexer) {
    SExprToken token = readToken(lexer);
	return newCons(keywords[KWD_QUOTE], newCons(parseToken(lexer, token), NULL));
}

static ScmValue *parseToken(ScmLexer *lexer, SExprToken token) {
    switch (token) {
		case T_LPAREN: return parseList(lexer);
		case T_QUOTE: return parseQuoted(lexer);
		case T_SYMBOL: return lexer->value;
		default: return NULL;
	}
}

static ScmValue *parser(ScmLexer *lexer) {
    SExprToken token = readToken(lexer);
    return parseToken(lexer, token);
}

// Eval
ScmValue *eval(ScmValue *context, ScmValue *code);

static ScmValue *evalVar(ScmValue *context, ScmValue *var) {
    ScmValue *v;
    while (context != NULL) {
		for (v = context->v.context.vars; v != NULL; v = CDR(v)) 
            if (CAR(CAR(v)) == var) return CDR(CAR(v));
		context = context->v.context.parent;
    }
	fprintf(stderr, "Undefined variable: %s\n", var->v.symname->v.s);
	return NULL;
}

static ScmValue *setVar(ScmValue *context, ScmValue *var, ScmValue *val) {
    ScmValue *v;
	for (v = context->v.context.vars; v != NULL; v = CDR(v))
		if (CAR(CAR(v)) == var) {
			CDR(CAR(v)) = val;
			return val;
		}
	context->v.context.vars = newCons(newCons(var, val), context->v.context.vars);
	return val;
}

static ScmValue *deferEval(ScmValue *context, ScmValue *code) {
    if (code->type != SCM_CELL) return eval(context, code);
	deferredCall.v.func.context = context;
	deferredCall.v.func.code = code;
	return &deferredCall;
}

static ScmValue *evalFunc(ScmValue *context, ScmValue *code) {
    for (; code != NULL; code = CDR(code)) {
		if (CDR(code) == NULL) return deferEval(context, CAR(code)); // Tail-recursion
		else eval(context, CAR(code));
	}
	return NULL;
}

static ScmValue *evalArgs(ScmValue *context, ScmValue *code) {
    ScmValue *args = NULL, **a = &args, *c;
	for (c = code; c != NULL; c = CDR(c)) {
		*a = newValue(SCM_CELL);
		CAR(*a) = eval(context, CAR(c));
		a = &CDR(*a);
	}
	*a = NULL;
	return args;
}

static ScmValue *apply(ScmValue *context, ScmValue *code) {
    ScmValue *func = eval(context, CAR(code));
    if (func->type == SCM_BUILTIN) {
		ScmValue *res, *args = evalArgs(context, CDR(code));
		res = func->v.builtin(args);
		return res;
	} else if (func->type == SCM_FUNCTION) {
		ScmValue *n, *c, *res;
		ScmValue *newcontext = newValue(SCM_CONTEXT);
		newcontext->v.context.parent = func->v.func.context;
		newcontext->v.context.vars = NULL;
		c = CDR(code);
		for (n = CAR(func->v.func.code); n != NULL; n = CDR(n)) {
			if (n->type == SCM_SYMBOL) {
				setVar(newcontext, n, evalArgs(context, c));
				break;
			}
			setVar(newcontext, CAR(n), eval(context, CAR(c)));
			c = CDR(c);
		}
		res = evalFunc(newcontext, CDR(func->v.func.code));
		return res;
	} else {
		fprintf(stderr, "Invalid function call\n");
		return NULL;
	}
}

static ScmValue *evalListHelper(ScmValue *context, ScmValue *code) {
    ScmValue *first = CAR(code);
	if (first == keywords[KWD_QUOTE]) {
		return CAR(CDR(code));
	}else if (first == keywords[KWD_IF]) {
		ScmValue *val = eval(context, CAR(CDR(code)));
		assert(val != NULL && (val->type == SCM_NUMBER || val->type == SCM_BOOL));
		if (val->v.i) return deferEval(context, CAR(CDR(CDR(code))));
		else if (CDR(CDR(CDR(code))) != NULL) return deferEval(context, CAR(CDR(CDR(CDR(code)))));
	}else if (first == keywords[KWD_LAMBDA]) {
		ScmValue *res = newValue(SCM_FUNCTION);
		res->v.func.context = context;
		res->v.func.code = CDR(code);
		return res;
	}else if (first == keywords[KWD_DEFINE]) {
		if (CAR(CDR(code))->type == SCM_CELL) {
			ScmValue *func = newValue(SCM_FUNCTION);
			func->v.func.context = context;
			func->v.func.code = newCons(CDR(CAR(CDR(code))), CDR(CDR(code)));
			return setVar(context, CAR(CAR(CDR(code))), func); // Clojure
		} else return setVar(globalContext, CAR(CDR(code)), eval(context, CAR(CDR(CDR(code)))));
	}else if (first == keywords[KWD_LET]) {
		ScmValue *newcontext = newValue(SCM_CONTEXT);
		ScmValue *vars, *res;
		newcontext->v.context.parent = context;
		for (vars = CAR(CDR(code)); vars != NULL; vars = CDR(vars)) 
            setVar(newcontext, CAR(CAR(vars)), eval(newcontext, CAR(CDR(CAR(vars)))));
		res = evalFunc(newcontext, CDR(CDR(code)));
		return res;
	}else if (first == keywords[KWD_BEGIN]) return evalFunc(context, CDR(code));
	return apply(context, code);
}

static ScmValue *evalList(ScmValue *context, ScmValue *code)
{
	ScmValue *res = evalListHelper(context, code);
	while (res == &deferredCall) { // Tail-recursion
		context = deferredCall.v.func.context;
		code = deferredCall.v.func.code;
		res = evalListHelper(context, code);
	}
	return res;
}

ScmValue *eval(ScmValue *context, ScmValue *code) {
	switch (code->type) {
		case SCM_SYMBOL: return evalVar(context, code);
		case SCM_CELL: return evalList(context, code);
		default: break;
	}
	return code;
}

// Builtin Functions
static ScmValue *builtinAdd(ScmValue *args)  { return newNumber(SCM_NUMBER, CAR(args)->v.i + CAR(CDR(args))->v.i); }
static ScmValue *builtinSub(ScmValue *args)  { return newNumber(SCM_NUMBER, CAR(args)->v.i - CAR(CDR(args))->v.i); }
static ScmValue *builtinMult(ScmValue *args) { return newNumber(SCM_NUMBER, CAR(args)->v.i * CAR(CDR(args))->v.i); }
static ScmValue *builtinDiv(ScmValue *args)  { return newNumber(SCM_NUMBER, CAR(args)->v.i / CAR(CDR(args))->v.i); }

static ScmValue *builtinAnd(ScmValue *args)  { return newNumber(SCM_BOOL, CAR(args)->v.i && CAR(CDR(args))->v.i);  }
static ScmValue *builtinOr(ScmValue *args)   { return newNumber(SCM_BOOL, CAR(args)->v.i || CAR(CDR(args))->v.i);  }
static ScmValue *builtinEq(ScmValue *args)   { return newNumber(SCM_BOOL, innerEqual(CAR(args), CAR(CDR(args))));  }
static ScmValue *builtinLt(ScmValue *args)   { return newNumber(SCM_BOOL, innerLt(CAR(args), CAR(CDR(args))));     }
static ScmValue *builtinNot(ScmValue *args)  { return newNumber(SCM_BOOL, !CAR(args)->v.i);                        }

static ScmValue *builtinCar(ScmValue *args)  { return CAR(CAR(args));                                              }
static ScmValue *builtinCdr(ScmValue *args)  { return CDR(CAR(args));                                              }
static ScmValue *builtinCons(ScmValue *args) { return newCons(CAR(args), CAR(CDR(args)));                          }

static ScmValue *builtinEval(ScmValue *args) { return eval(globalContext, CAR(args));                              }
static ScmValue *builtinPrint(ScmValue *args){ innerPrint(CAR(args)); printf("\n"); return NULL;                   }
static ScmValue *builtinExit(ScmValue *args) { exit(0); return NULL;                                               }

static ScmValue *builtinRead(ScmValue *args) {
	ScmLexer lexer;
	char buf[256];
	printf("> "); fflush(stdout);
	fgets(buf, sizeof(buf), stdin); buf[sizeof(buf) - 1] = '\0';
	initLexer(&lexer, buf);
	return parser(&lexer);
}

static void defineBuiltin(char *name, ScmBuiltin func) {
	ScmValue *builtin = newValue(SCM_BUILTIN);
	builtin->v.builtin = func;
	setVar(globalContext, findSymbol(name, strlen(name)), builtin);
}

// Interface
void init() {
	int i;
	for (i = 0; i < NUM_KEYWORDS; i++) keywords[i] = findSymbol(keyword_names[i], strlen(keyword_names[i]));
	globalContext = newValue(SCM_CONTEXT);
	defineBuiltin("add", builtinAdd);
	defineBuiltin("sub", builtinSub);
	defineBuiltin("mult", builtinMult);
	defineBuiltin("div", builtinDiv);
	defineBuiltin("lt?", builtinLt);
	defineBuiltin("eq?", builtinEq);
	defineBuiltin("and", builtinAnd);
	defineBuiltin("or", builtinOr);
	defineBuiltin("not", builtinNot);
	defineBuiltin("car", builtinCar);
	defineBuiltin("cdr", builtinCdr);
	defineBuiltin("cons", builtinCons);
	defineBuiltin("eval", builtinEval);
	defineBuiltin("say", builtinPrint);  // A favour for Perl(x
    defineBuiltin("read", builtinRead);
	defineBuiltin("exit", builtinExit);
}

static char *readFile(char *filename) {
	char *res;
	unsigned int file_size;
	FILE *fs = fopen(filename, "r");
	if (fs == NULL) {
		perror("fopen");
		exit(-1);
	}
	fseek(fs, 0, SEEK_END);
	file_size = ftell(fs);
	fseek(fs, 0, SEEK_SET);
	res = malloc(file_size + 1);
	fread(res, 1, file_size, fs);
	res[file_size] = '\0';
	return res;
}

static void process(char *filename) {
	ScmValue *code = NULL;
	ScmLexer lexer;
	char *content = readFile(filename);
	initLexer(&lexer, content);
	while ((code = parser(&lexer)) != NULL) eval(globalContext, code);
}

int main(int argc, char *argv[]) {
    if (argc < 2) {
        printf("Usage: yuki <filename>\n");
        exit(-1);
    }
    init();
    process(argv[1]);
    return 0;
}
