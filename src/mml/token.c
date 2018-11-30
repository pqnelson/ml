#include <stdlib.h>
#include <string.h> /* memcmp(), strnlen() */
#include "defs.h"
#include "mml/token.h"

/**
 * Allocates new @c mml_Token object.
 */
mml_Token* mml_Token_new(MML_TokenType type, const char *start,
                         size_t length, size_t line) {
    mml_Token *token = malloc(sizeof(*token));
    if (NULL == token) exit(EXIT_MALLOCERR);
    //@ assert (length > 0) || type = MML_TOKEN_EOF
    token->type = type;
    token->start = start;
    token->length = length;
    token->line = line;
    return token;
}

/**
 * Frees @c mml_Token object.
 */
void mml_Token_free(mml_Token *token) {
    if (NULL == token) return;
    free(token);
    token = NULL;
}

/**
 * Tests if two @c mml_Token objects are equal.
 *
 * Equality specifically tests if they are the same token type, and if so
 * whether the lexemes are the same.
 */
bool mml_Token_equals(mml_Token *lhs, mml_Token *rhs) {
    if (NULL == lhs) return false;
    if (NULL == rhs) return false;
    if (mml_Token_type(lhs) == mml_Token_type(rhs))
        return mml_Token_hasSameLexeme(lhs, rhs);
    else
        return false;
}
// setters
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
void mml_Token_setLine(mml_Token *this, size_t line) {
    if (NULL == this) return;
    this->line = line;
}

// getters
/**
 * Obtain the @c MML_TokenType for the given token object.
 *
 * @param token A pointer to the @c mml_Token object.
 * @return @c EOF token for @c NULL pointers passed in, otherwise it
 * returns a copy of the token's type. 
 */
MML_TokenType mml_Token_type(mml_Token *token) {
    if (NULL == token) return MML_TOKEN_EOF;
    return token->type;
}

/**
 * Obtain the string length of the underlying lexeme.
 */
size_t mml_Token_length(mml_Token *token) {
    return token->length;
}

/**
 * Line number for the given token object.
 */
size_t mml_Token_line(mml_Token *token) {
    return token->line;
}

// predicates
/**
 * Tests if two token objects have equal lexemes.
 *
 * Specifically tests using string equality rather than pointer equality,
 * so we can say, e.g., "These two identifier tokens refer to the same
 * variable in different parts of the input."
 *
 * If either parameter is @c NULL, this short-circuits to false. (Even
 * if @em both are @c NULL, this short-circuits to false!)
 *
 * @param lhs A pointer to the left-hand side of the test equality.
 * @param rhs A pointer to the right-hand side of the test equality.
 * @return @c true if and only if the two tokens are non-null and share the same lexeme.
 */
bool mml_Token_hasSameLexeme(mml_Token *lhs, mml_Token *rhs) {
    if (NULL == lhs) return false;
    if (NULL == rhs) return false;
    if ((lhs->length) != (rhs->length)) return false;
    return 0 == memcmp(lhs->start, rhs->start, lhs->length);
}

/**
 * Test if the underlying lexeme is equal to a given string.
 *
 * Check if the lexeme underlying the mml_Token is equal to a given string.
 * 
 * @param this A valid mml_Token object.
 * @param lexeme The string we're comparing the token to.
 * @return @true if and only if both @c this and @c lexeme are non-NULL and the lexeme underlying @c this is equal to @c lexeme as an array of bytes.
 */
bool mml_Token_lexemeEquals(mml_Token *this, const char *lexeme) {
    if (NULL == this) return false;
    if (NULL == lexeme) return false;
    if (strnlen(lexeme, this->length+2) > (this->length)) {
        return false;
    } else {
        return 0 == memcmp(lexeme, this->start, this->length);
    }
}

bool mml_Token_isError(mml_Token *token) {
    if (NULL == token) return false;
    return MML_TOKEN_ERROR == token->type;
}

bool mml_Token_isEOF(mml_Token *token) {
    if (NULL == token) return false;
    return MML_TOKEN_EOF == token->type;
}

bool mml_Token_isIdentifier(mml_Token *token) {
    if (NULL == token) return false;
    return MML_TOKEN_IDENTIFIER == token->type;
}

bool mml_Token_isNumber(mml_Token *token) {
    if (NULL == token) return false;
    return MML_TOKEN_INTEGER == token->type;
}

/**
 * Tests if token consists of punctuation.
 *
 * A "symbol" meaning it is a "reserved symbol" like the esti (<code>::</code>) symbol.
 */
bool mml_Token_isSymbol(mml_Token *token) {
    if (NULL == token) return false;
    return (MML_TOKEN_PUNCT_START < (token->type)
            && (token->type) < MML_TOKEN_PUNCT_END);
}

/**
 * Tests if token is a reserved keyword or not.
 */
bool mml_Token_isKeyword(mml_Token *token) {
    if (NULL == token) return false;
    return (MML_TOKEN_KW_START < (token->type)
            && (token->type) < MML_TOKEN_KW_END);
}
