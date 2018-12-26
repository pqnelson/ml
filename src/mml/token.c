#include <stdlib.h>
#include <string.h> /* memcmp(), strlen() */
#include "utils.h"
#include "mml/token.h"

// TODO: add validation, to check the MML_TokenType matches reserved
//       keywords and symbols. (Right now, it's completely naive and
//       undefensive.)
/*@ requires (length > 0 || MML_TOKEN_EOF == type);
  @ requires line > 0
  @ behavior bad_lexeme:
  @   assumes !\valid(start) && MML_TOKEN_EOF != type;
  @   ensures \null == \result;
  @ behavior allocation:
  @   assumes \valid(start) || MML_TOKEN_EOF == type;
  @   assumes is_allocable(sizeof(struct mml_Token));
  @   assigns \result;
  @   allocates \result;
  @   ensures \valid(\result);
  @   ensures type == \result->type;
  @   ensures start == \result->start;
  @   ensures length == \result->length;
  @   ensures line == \result->line;
  @ behavior no_allocation:
  @   assumes \valid(start) || MML_TOKEN_EOF == type;
  @   assumes !is_allocable(sizeof(struct mml_Token));
  @   exits EXIT_MALLOCERR;
  @ disjoint behaviors;
  @ complete behaviors;
  @*/
mml_Token* mml_Token_new(MML_TokenType type, const char *start,
                         size_t length, size_t line) {
    //@ assert (length > 0) || type = MML_TOKEN_EOF
    if (NULL == start && type != MML_TOKEN_EOF) {
        eprintf("make_Token_new() passed in NULL start\n");
        return (mml_Token*)NULL;
    }
    //@ assert NULL == start ==> MML_TOKEN_EOF == type;
    // allocate memory, or explode
    mml_Token *token = malloc(sizeof(*token));
    if (NULL == token) {
        //@ assert !\allocable(sizeof(struct mml_Token));
        exit(EXIT_MALLOCERR);
    }
    //@ assert \allocable(sizeof(struct mml_Token));
    // initialize the fields
    token->type = type;
    token->start = start;
    token->length = length;
    token->line = line;
    
    return token;
}

/*@ frees(token);
  @ assigns *token;
  @ ensures \null == token;
  @*/
void mml_Token_free(mml_Token *token) {
    if (NULL == token) return;
    free(token);
    token = NULL;
}

/*@ behavior null_lhs:
  @   assumes \null == lhs;
  @   ensures false == \result;
  @ behavior null_rhs:
  @   assumes \null == rhs;
  @   ensures false == \result;
  @ behavior matching_token_types:
  @   assumes \valid(lhs) && \valid(rhs);
  @   assumes mml_Token_type(lhs) == mml_Token_type(rhs);
  @   ensures \result == mml_Token_hasSameLexeme(lhs, rhs);
  @ behavior mismatching_token_types:
  @   assumes \valid(lhs) && \valid(rhs);
  @   assumes mml_Token_type(lhs) == mml_Token_type(rhs);
  @   ensures false == \result;
  @ disjoint behaviors;
  @ complete behaviors;
  @*/
bool mml_Token_equals(mml_Token *lhs, mml_Token *rhs) {
    if (NULL == lhs) return false;
    if (NULL == rhs) return false;
    if (mml_Token_type(lhs) == mml_Token_type(rhs))
        return mml_Token_hasSameLexeme(lhs, rhs);
    else
        return false;
}

// setters
/*@ behavior null_token:
  @   assumes !\valid(this);
  @   assigns \nothing;
  @ behavior default:
  @   assumes \valid(this);
  @   assigns *this;
  @   ensures line == this->line;
  @ disjoint behaviors;
  @ complete behaviors;
  @*/
void mml_Token_setLine(mml_Token *this, size_t line) {
    if (NULL == this) return;
    this->line = line;
}

// getters
/*@ behavior null_token:
  @   assumes !\valid(token);
  @   ensures MML_TOKEN_EOF == \result;
  @ behavior default:
  @   assumes \valid(token);
  @   ensures token->type == \result;
  @ disjoint behaviors;
  @ complete behaviors;
  @*/
MML_TokenType mml_Token_type(mml_Token *token) {
    if (NULL == token) return MML_TOKEN_EOF;
    return token->type;
}

/*@ behavior null_token:
  @   assumes !\valid(token);
  @   ensures 0 == \result;
  @ behavior default:
  @   assumes \valid(token);
  @   ensures token->length == \result;
  @ disjoint behaviors;
  @ complete behaviors;
  @*/
size_t mml_Token_length(mml_Token *token) {
    if (NULL == token) return 0;
    return token->length;
}

/*@ behavior null_token:
  @   assumes !\valid(token);
  @   ensures 0 == \result;
  @ behavior default:
  @   assumes \valid(token);
  @   ensures token->line == \result;
  @ disjoint behaviors;
  @ complete behaviors;
  @*/
size_t mml_Token_line(mml_Token *token) {
    if (NULL == token) return 0;
    return token->line;
}

// predicates
/*@ behavior lhs_is_null:
  @   assumes !\valid(lhs);
  @   ensures false == \result;
  @ behavior rhs_is_null:
  @   assumes !\valid(rhs);
  @   ensures false == \result;
  @ behavior lexeme_length_mismatch:
  @   assumes \valid(lhs);
  @   assumes \valid(rhs);
  @   assumes mml_Token_length(lhs) != mml_Token_length(rhs);
  @   ensures false == \result;
  @ behavior default:
  @   assumes \valid(lhs);
  @   assumes \valid(rhs);
  @   assumes mml_Token_length(lhs) == mml_Token_length(rhs);
  @   ensures \result == (0 == memcmp(lhs->start, rhs->start, lhs->length));
  @ disjoint behaviors;
  @ complete behaviors;
  @*/
bool mml_Token_hasSameLexeme(mml_Token *lhs, mml_Token *rhs) {
    if (NULL == lhs) return false;
    if (NULL == rhs) return false;
    if ((lhs->length) != (rhs->length)) return false;
    return 0 == memcmp(lhs->start, rhs->start, lhs->length);
}

/*@ behavior null_token:
  @   assumes !\valid(this);
  @   ensures false == \result;
  @ behavior null_lexeme:
  @   assumes \valid(this);
  @   assumes !\valid(lexeme);
  @   ensures false == \result;
  @ behavior strlen_mismatch:
  @   assumes \valid(this);
  @   assumes \valid(lexeme);
  @   assumes \strlen(lexeme) != mml_Token_length(this);
  @   ensures false == \result;
  @ behavior default:
  @   assumes \valid(this);
  @   assumes \valid(lexeme);
  @   assumes \strlen(lexeme) == mml_Token_length(this);
  @   ensures \result == (0 == memcmp(lexeme, this->start, this->length));
  @ disjoint behaviors;
  @ complete behaviors;
  @*/
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

/*@ behavior null_token:
  @   assumes !\valid(token)
  @   ensures false == \result;
  @ behavior default:
  @   assumes \valid(token);
  @   ensures \result == (MML_TOKEN_ERROR == token->type);
  @ disjoint behaviors;
  @ complete behaviors;
  @*/
bool mml_Token_isError(mml_Token *token) {
    if (NULL == token) return false;
    return MML_TOKEN_ERROR == token->type;
}

/*@ behavior null_token:
  @   assumes !\valid(token)
  @   ensures false == \result;
  @ behavior default:
  @   assumes \valid(token);
  @   ensures \result == (MML_TOKEN_EOF == token->type);
  @ disjoint behaviors;
  @ complete behaviors;
  @*/
bool mml_Token_isEOF(mml_Token *token) {
    if (NULL == token) return false;
    return MML_TOKEN_EOF == token->type;
}

/*@ behavior null_token:
  @   assumes !\valid(token)
  @   ensures false == \result;
  @ behavior default:
  @   assumes \valid(token);
  @   ensures \result == (MML_TOKEN_IDENTIFIER == token->type);
  @ disjoint behaviors;
  @ complete behaviors;
  @*/
bool mml_Token_isIdentifier(mml_Token *token) {
    if (NULL == token) return false;
    return MML_TOKEN_IDENTIFIER == token->type;
}

/*@ behavior null_token:
  @   assumes !\valid(token)
  @   ensures false == \result;
  @ behavior default:
  @   assumes \valid(token);
  @   ensures \result == (MML_TOKEN_INTEGER == token->type);
  @ disjoint behaviors;
  @ complete behaviors;
  @*/
bool mml_Token_isNumber(mml_Token *token) {
    if (NULL == token) return false;
    return MML_TOKEN_INTEGER == token->type;
}

/*@ behavior null_token:
  @   assumes !\valid(token)
  @   ensures false == \result;
  @ behavior default:
  @   assumes \valid(token);
  @   ensures \result == (MML_TOKEN_PUNCT_START < token->type
  @                       && token->type < MML_TOKEN_PUNCT_END);
  @ disjoint behaviors;
  @ complete behaviors;
  @*/
bool mml_Token_isSymbol(mml_Token *token) {
    if (NULL == token) return false;
    return (MML_TOKEN_PUNCT_START < (token->type)
            && (token->type) < MML_TOKEN_PUNCT_END);
}

/*@ behavior null_token:
  @   assumes !\valid(token)
  @   ensures false == \result;
  @ behavior default:
  @   assumes \valid(token);
  @   ensures \result == (MML_TOKEN_KW_START < token->type
  @                       && token->type < MML_TOKEN_KW_END);
  @ disjoint behaviors;
  @ complete behaviors;
  @*/
bool mml_Token_isKeyword(mml_Token *token) {
    if (NULL == token) return false;
    return (MML_TOKEN_KW_START < (token->type)
            && (token->type) < MML_TOKEN_KW_END);
}
