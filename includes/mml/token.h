/**
 * @file includes/mml/token.h
 * 
 * Tokens for Mini-ML.
 *
 * Since C has no namespacing, everything is prefixed with @c MML_
 * (for "Mini-ML") followed by @c Token_.
 *
 * The EBNF for Mini-ML can be found in includes/mml/scanner.h
 *
 * @author Alex Nelson <pqnelson@gmail.com>
 * @date July 30, 2018
 */
#ifndef MML_TOKEN_H
#define MML_TOKEN_H

#define MML_TOKENTYOE_START  0
#define MML_TOKENTYPE_SIZE 256

typedef enum {
    /* punctuation tokens (at most 128 of them) */
    MML_TOKEN_PUNCT_START = -1,
    MML_TOKEN_EOF         = 0,
    MML_TOKEN_LEFT_PAREN  = 1,
    MML_TOKEN_RIGHT_PAREN = 2,
    MML_TOKEN_SEMICOLON   = 3,
    MML_TOKEN_COLON       = 4,
    MML_TOKEN_MINUS       = 5,
    MML_TOKEN_PLUS        = 6,
    MML_TOKEN_EQUAL       = 7,
    MML_TOKEN_LEFT_BRACE  = 8, /* '{' */
    MML_TOKEN_RIGHT_BRACE = 9, /* '}' */
    MML_TOKEN_STAR        = 10, /* '*' */
    MML_TOKEN_UNDERSCORE  = 11, /* '_' */
    MML_TOKEN_AT_SIGN     = 12, /* '@' */
    
    MML_TOKEN_ESTI        = 32, /* "::" */
    MML_TOKEN_FN_ARROW    = 33,

    MML_TOKEN_PUNCT_END = 128,
    
    /* reserved keywords (at most 64 of them) */
    MML_TOKEN_KW_START = 127,
    MML_TOKEN_TRUE     = 128,
    MML_TOKEN_FALSE    = 129,
    MML_TOKEN_INT      = 130,
    MML_TOKEN_BOOL     = 131,
    MML_TOKEN_FN       = 132,
    MML_TOKEN_IF       = 133,
    MML_TOKEN_THEN     = 134,
    MML_TOKEN_ELSE     = 135,
    MML_TOKEN_LET      = 136,
    MML_TOKEN_LETREC   = 137,
    MML_TOKEN_IN       = 138,
    MML_TOKEN_CASE     = 139,
    MML_TOKEN_DATA     = 140,
    MML_TOKEN_NEWTYPE  = 141,
    MML_TOKEN_FORALL   = 142,
    MML_TOKEN_OF       = 143,

    MML_TOKEN_KW_END = 192,
    
    /* non-reserved, non-puncuation keywords */
    MML_TOKEN_INTEGER    = 192,
    MML_TOKEN_IDENTIFIER = 193,
    MML_TOKEN_STRING     = 194,
    
    MML_TOKEN_ERROR = 255
} MML_TokenType;

/* everything in a token should be constant/invariant/unchangeable */
typedef struct mml_Token {
    MML_TokenType type;
    const char *start;
    size_t length;
    size_t line;
} mml_Token;

mml_Token* mml_Token_new(MML_TokenType type, const char *start, size_t length, size_t line);
void mml_Token_free(mml_Token *token);
bool mml_Token_equals(mml_Token *lhs, mml_Token *rhs);

/* setters */
void mml_Token_setLine(mml_Token *this, size_t line);

/* getters */
MML_TokenType mml_Token_type(mml_Token *token);
size_t mml_Token_length(mml_Token *token);
size_t mml_Token_line(mml_Token *token);

/* predicates */
bool mml_Token_hasSameLexeme(mml_Token *lhs, mml_Token *rhs);
bool mml_Token_lexemeEquals(mml_Token *this, const char *lexeme);

bool mml_Token_isError(mml_Token *token);
bool mml_Token_isEOF(mml_Token *token);
bool mml_Token_isIdentifier(mml_Token *token);
bool mml_Token_isNumber(mml_Token *token);
bool mml_Token_isSymbol(mml_Token *token);
bool mml_Token_isKeyword(mml_Token *token);
#endif /* MML_TOKEN_H */
