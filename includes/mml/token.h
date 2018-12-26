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

// For use in exclusive comparisons, e.g.,
// MML_TOKENTYPE_START < type && type < MML_TOKENTYPE_SIZE
#define MML_TOKENTYPE_START -1
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

/**
 * Allocates new @c mml_Token object.
 *
 * Attempt to allocate a new mml_Token object on the heap. There are two
 * edge-case "gotchas" to bear in mind:
 * 1. If @c start is a @c NULL pointer @em and the @c type is not an EOF
 *    token, then the result is a @c NULL pointer.
 * 2. If @c malloc() fails, this will @c exit() with @c EXIT_MALLOCERR
 *    status.
 *
 * @param type The MML_TokenType for the newly allocated token.
 * @param start The lexeme underlying the token.
 * @param length The lexeme's length as a char array.
 * @param line The line number where we parsed the lexeme.
 * @return Pointer to newly allocated mml_Token object.
 * 
 * @todo Add validation to check the @c MML_TokenType provided matches the
 *       lexeme.
 */
mml_Token* mml_Token_new(MML_TokenType type, const char *start,
                         size_t length, size_t line);

/**
 * Frees @c mml_Token object.
 *
 * Free the mml_Token object, but @em not the lexeme. Assigns the @c token
 * parameter to be @c NULL.
 *
 * If @c token is already @c NULL, safely does nothing.
 * 
 * @param token The mml_Token to be freed.
 * @return Nothing.
 */
void mml_Token_free(mml_Token *token);

/**
 * Tests if two @c mml_Token objects are equal.
 *
 * Equality specifically tests if they are the same token type, and if so
 * whether the lexemes are the same (considered as an array of bytes).
 *
 * Returns false if either mml_Token is @c NULL.
 *
 * @param lhs The left-hand side of the equality test.
 * @param rhs The right-hand side of the equality test.
 * @return @c true if and only if the mml_Token objects are (1) not @c NULL,
 *         (2) they have the same token type, (3) they have the same lexeme.
 */
bool mml_Token_equals(mml_Token *lhs, mml_Token *rhs);

/* setters */
/**
 * Assign line to a token.
 *
 * For error tokens, it is useful to indicate the line where the error
 * started. This just abstracts away the "inner workings" of the token
 * object.
 *
 * @param this A pointer to the mml_Token object mutating.
 * @param line The new line number for the object.
 * @return Nothing.
 */
void mml_Token_setLine(mml_Token *this, size_t line);

/* getters */
/**
 * Obtain the @c MML_TokenType for the given token object.
 *
 * For @c NULL pointers, the result defaults to @c MML_TOKEN_EOF. This
 * is consistent with the mml_Token_new() behavior.
 *
 * @param token A pointer to the @c mml_Token object.
 * @return @c EOF token for @c NULL pointers passed in, otherwise it
 *         returns a copy of the token's type. 
 */
MML_TokenType mml_Token_type(mml_Token *token);
/**
 * Obtain the string length of the underlying lexeme.
 *
 * For @c NULL pointers, the result defaults to 0;
 *
 * @param token A pointer to the @c mml_Token object.
 * @return The length of the lexeme underlying @c token.
 */
size_t mml_Token_length(mml_Token *token);
/**
 * Line number for the given token object.
 *
 * For @c NULL pointers, the result defaults to 0;
 *
 * @param token A pointer to the @c mml_Token object.
 * @return The line number for the lexeme underlying the @c token pointer.
 */
size_t mml_Token_line(mml_Token *token);

/* predicates */
/**
 * Tests if two token objects have equal lexemes.
 *
 * Specifically tests using string equality rather than pointer equality,
 * so we can say, e.g., "These two identifier tokens refer to the same
 * variable in different parts of the input."
 *
 * There is no test if the token types are the same. We may ostensibly have
 * the same lexeme for different token types.
 *
 * If either parameter is @c NULL, this short-circuits to false. (Even
 * if @em both are @c NULL, this short-circuits to false!)
 *
 * @param lhs A pointer to the left-hand side of the test equality.
 * @param rhs A pointer to the right-hand side of the test equality.
 * @return @c true if and only if the two tokens are non-null
 *         and share the same lexeme.
 */
bool mml_Token_hasSameLexeme(mml_Token *lhs, mml_Token *rhs);

/**
 * Test if the underlying lexeme is equal to a given string.
 *
 * Check if the lexeme underlying the mml_Token is equal to a given string.
 * 
 * @param this A valid mml_Token object.
 * @param lexeme The string we're comparing the token to.
 * @return @c true if and only if both @c this and @c lexeme are non-NULL
 *         and the lexeme underlying @c this is equal to
 *         @c lexeme as an array of bytes.
 */
bool mml_Token_lexemeEquals(mml_Token *this, const char *lexeme);

/**
 * Test if token is an error.
 *
 * Tests if the given token is really encoding an invalid character
 * sequence.
 *
 * @param token A Mini-ML token.
 * @return @c true if and only if the @c token is (1) not @c NULL, and
 *         (2) an error token.
 */
bool mml_Token_isError(mml_Token *token);

/**
 * Test if token is end of input.
 *
 * Tests if the given token is really encoding an EOF character,
 * i.e., the end of input stream.
 *
 * @param token A Mini-ML token.
 * @return @c true if and only if the @c token is (1) not @c NULL, and
 *         (2) an EOF token.
 */
bool mml_Token_isEOF(mml_Token *token);

/**
 * Test if token is an identifier.
 *
 * Tests if the given token is really encoding an identifier. For Mini-ML,
 * identifiers are any sequence of alphanumeric characters,
 * \"<code>_</code>\", or \"<code>'</code>\" characters.
 *
 * @b BUT the identifier @em must begin with an alphabetic character. So
 * @c alloc0 is a valid identifier, but @c 0alloc is not.
 *
 * This is following Haskell's conventions for identifiers.
 *
 * @param token A Mini-ML token.
 * @return @c true if and only if the @c token is (1) not @c NULL, and
 *         (2) an EOF token.
 * @see https://www.haskell.org/onlinereport/lexemes.html
 */
bool mml_Token_isIdentifier(mml_Token *token);

/**
 * Test if token is an integer or not.
 *
 * For now, the only number type supported is an integer.
 *
 * @param token A Mini-ML token.
 * @return @c true if and only if @c token is not @c NULL
 *         and it is an integer token.
 */
bool mml_Token_isNumber(mml_Token *token);

/**
 * Tests if token consists of punctuation.
 *
 * A "symbol" meaning it is a "reserved symbol" like the
 * esti (<code>::</code>) symbol.
 *
 * @param token A Mini-ML token.
 * @return @c true if and only if the token's type is a reserved symbol.
 */
bool mml_Token_isSymbol(mml_Token *token);

/**
 * Tests if token is a reserved keyword or not.
 * 
 * @param token A Mini-ML token.
 * @return @c true if and only if the token's type is a reserved keyword.
 */
bool mml_Token_isKeyword(mml_Token *token);
#endif /* MML_TOKEN_H */
