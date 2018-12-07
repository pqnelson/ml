#include <stdlib.h>
#include <string.h> /* memcmp(), strlen() */
#include "defs.h"
#include "mml/token.h"

/**
 * Allocates new @c mml_Token object.
 */
mml_Token* mml_Token_new(MML_TokenType type, const char *start,
                         size_t length, size_t line) {
    //@ assert (length > 0) || type = MML_TOKEN_EOF
    if (NULL == start) {
        eprintf("make_Token_new() passed in NULL start\n");
        return (mml_Token*)NULL;
    }
    // allocate memory, or explode
    mml_Token *token = malloc(sizeof(*token));
    if (NULL == token) exit(EXIT_MALLOCERR);
    // initialize the fields
    token->type = type;
    token->start = start;
    token->length = length;
    token->line = line;
    
    return token;
}

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
void mml_Token_free(mml_Token *token) {
    if (NULL == token) return;
    free(token);
    token = NULL;
}

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
 *         returns a copy of the token's type. 
 */
MML_TokenType mml_Token_type(mml_Token *token) {
    if (NULL == token) return MML_TOKEN_EOF;
    return token->type;
}

/**
 * Obtain the string length of the underlying lexeme.
 */
size_t mml_Token_length(mml_Token *token) {
    if (NULL == token) return 0;
    return token->length;
}

/**
 * Line number for the given token object.
 */
size_t mml_Token_line(mml_Token *token) {
    if (NULL == token) return 0;
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
 * @return @c true if and only if the two tokens are non-null
 *         and share the same lexeme.
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
 * @return @c true if and only if both @c this and @c lexeme are non-NULL
 *         and the lexeme underlying @c this is equal to
 *         @c lexeme as an array of bytes.
 */
bool mml_Token_lexemeEquals(mml_Token *this, const char *lexeme) {
    if (NULL == this) return false;
    if (NULL == lexeme) return false;
    // XXX strlen() is a standard function, it might be worth while to
    // have our own strnlen() optimized for this, if this is used frequently
    if (strlen(lexeme) != (this->length)) {
        return false;
    } else {
        return 0 == memcmp(lexeme, this->start, this->length);
    }
}

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
bool mml_Token_isError(mml_Token *token) {
    if (NULL == token) return false;
    return MML_TOKEN_ERROR == token->type;
}

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
bool mml_Token_isEOF(mml_Token *token) {
    if (NULL == token) return false;
    return MML_TOKEN_EOF == token->type;
}

/**
 * Test if token is an identifier.
 *
 * Tests if the given token is really encoding an identifier. For Mini-ML,
 * identifiers are any sequence of alphabetic characters, \"@c _ \", or
 * \"@c ' \" characters.
 *
 * @param token A Mini-ML token.
 * @return @c true if and only if the @c token is (1) not @c NULL, and
 *         (2) an EOF token.
 */
bool mml_Token_isIdentifier(mml_Token *token) {
    if (NULL == token) return false;
    return MML_TOKEN_IDENTIFIER == token->type;
}

/**
 * Test if token is an integer or not.
 *
 * For now, the only number type supported is an integer.
 *
 * @param token A Mini-ML token.
 * @return @c true if and only if @c token is not @c NULL
 *         and it is an integer token.
 */
bool mml_Token_isNumber(mml_Token *token) {
    if (NULL == token) return false;
    return MML_TOKEN_INTEGER == token->type;
}

/**
 * Tests if token consists of punctuation.
 *
 * A "symbol" meaning it is a "reserved symbol" like the
 * esti (<code>::</code>) symbol.
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
