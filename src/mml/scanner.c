#include <ctype.h>
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <string.h> /* memcmp(), strnlen() */
#include "utils.h"
#include "mml/token.h"
#include "mml/scanner.h"
// TODO: write `logic` functions for the skip whitespace and comments
// TODO: write `logic` function for the first char after skipping whitespace
// TODO: rewrite the contract for mml_Scanner_next(), it could be more
//       readable (if not elegant).

/*@ behavior null_source:
  @   assumes !\valid(source);
  @   assigns \nothing;
  @   ensures \null == \result;
  @ behavior no_allocation:
  @   assumes \valid(source);
  @   assumes !is_allocable(sizeof(struct mml_Scanner));
  @   exits EXIT_MALLOCERR;
  @ behavior default:
  @   assumes \valid(source);
  @   assumes is_allocable(sizeof(struct mml_Scanner));
  @   allocates \result;
  @   ensures source == \result->start;
  @   ensures source == \result->current;
  @   ensures 1 == \result->line;
  @ disjoint behaviors;
  @ complete behaviors;
  @*/
mml_Scanner* mml_Scanner_new(const char *source) {
    if (NULL == source) {
        eprintf("Trying to pass null string to mml_Scanner_new()\n");
        return NULL;
    }
    mml_Scanner *scanner = malloc(sizeof(*scanner));
    if (NULL == scanner) {
        exit(EXIT_MALLOCERR);
    }
    scanner->start = source;
    scanner->current = source;
    scanner->line = 1;
    
    return scanner;
}

/*@ behavior null_pointer:
  @   assumes !\valid(this);
  @ behavior default:
  @   assumes \valid(this);
  @   frees this;
  @   ensures \null == this;
  @ disjoint behaviors;
  @ complete behaviors;
  @*/
void mml_Scanner_free(mml_Scanner *this) {
    if (NULL == this) return;
    free(this);
    this = NULL;
}

/*@ behavior null_pointer:
  @   assumes !\valid(this);
  @   ensures false == \result;
  @ behavior has_next:
  @   assumes \valid(this);
  @   assumes \exists size_t k,
  @           0 <= k <= strlen(this->current) ==> !isspace(this->current[k]);
  @   ensures true == \result;
  @ behavior no_next:
  @   assumes \valid(this);
  @   assumes \forall size_t k,
  @           0 <= k <= strlen(this->current) ==> isspace(this->current[k]);
  @   ensures false == \result;
  @ disjoint behaviors;
  @ complete behaviors;
  @*/
bool mml_Scanner_hasNext(mml_Scanner *this) {
    if (NULL == this) return false;
    bool hasNext = false;
    size_t c;
    for (c = 0; '\0' != this->current[c] && !hasNext; c++) {
        if (!isspace(this->current[c])) {
            hasNext = true;
        }
    }
    //@ assert ('\0' != this->current[c]) ==> !isspace(this->current[c])
    return hasNext;
}

/* ############################################################
   Everything else is just a helper to mml_Scanner_next()
   ############################################################ */

/*@ behavior null_scanner:
  @   assumes NULL == this;
  @   ensures '\0' == \result;
  @ behavior default:
  @   assumes \valid(this);
  @   ensures \result == this->current[0]
  @ disjoint behaviors;
  @ complete behaviors;
  @*/
static char peek(mml_Scanner *this) {
    if (NULL == this) return '\0';
    return this->current[0];
}

/*@ behavior does_not_have_next:
  @   assumes !mml_Scanner_hasNext(this);
  @   ensures '\0' == \result;
  @ behavior default:
  @   assumes mml_Scanner_hasNext(this);
  @   ensures \result == this->current[1];
  @ disjoint behaviors;
  @ complete behaviors;
  @*/
static char peekNext(mml_Scanner *this) {
    return (mml_Scanner_hasNext(this) ? this->current[1] : '\0');
}

/*@ behavior null_scanner:
  @   assumes NULL == this;
  @   ensures '\0' == \result;
  @ behavior default:
  @   assumes \valid(this);
  @   assigns this->current;
  @   ensures \result == \old(this->current);
  @   ensures this->current == \old(this->current) + 1;
  @ disjoint behaviors;
  @ complete behaviors;
  @*/
static char advance(mml_Scanner *this) {
    if (NULL == this) return '\0';
    this->current++;
    return this->current[-1];
}

/*@ logic integer commentStarts(const char *c, size_t offset) =
  @   ('\0' == start[offset] || '\0' == start[offset+1]) ? 0
  @   : (('('==start[offset] && '*' == start[offset+1]) ? 1 : 0);
  @*/

/*@ requires \valid(this)
  @ ensures \result == (1 == commentStarts(this->current, 0));
  @*/
static bool isCommentStart(mml_Scanner *this) {
    return (('(' == peek(this)) && ('*' == peekNext(this)));
}

enum SKIP_COMMENT_STATUS {
    SKIP_COMMENT_SUCCESS = 0,
    SKIP_COMMENT_RUNAWAY,
    SKIP_COMMENT_NONE_FOUND
};

/*@ logic boolean isCommentEnd(mml_Scanner *this) =
  @   ('*'==peek(this) && ')' == peekNext(this));
  @*/

/*@ requires \valid(this);
  @ behavior newline:
  @   assumes '\n' == peek(\old(this));
  @   assigns this->line;
  @   ensures this->line == 1 + \old(this->line);
  @   ensures \result == depth;
  @ behavior increase_depth:
  @   assumes isCommentStart(\old(this));
  @   assigns this->current;
  @   ensures \result == depth + 1;
  @   ensures !isCommentStart(this);
  @ behavior decrease_depth:
  @   assumes isCommentEnd(\old(this));
  @   assigns this->current;
  @   ansures \result == depth - 1;
  @   ensures !isCommentEnd(this);
  @ behavior default_behavior:
  @   assumes !isCommentStart(\old(this));
  @   assumes !isCommentEnd(\old(this));
  @   assumes '\n' != peek(\old(this));
  @   ensures \result == depth;
  @ disjoint behaviors;
  @ complete behaviors;
  @*/
static size_t adjustCommentDepth(mml_Scanner *this, size_t depth) {
    size_t newDepth = depth;
    switch(peek(this)) {
    case '\n':
        this->line += 1;
        break;
    case '(':
        if ('*' == peekNext(this)) {
            newDepth += 1;
            advance(this);
        }
        break;
    case '*':
        if (')' == peekNext(this)) {
            newDepth -= 1;
            advance(this);
        }
        break;
    default: // keep advancing
        break;
    }
    return newDepth;
}

/*@ logic integer numOfCommentStarts(const char *start, size_t length) =
  @   \numof(0, length, \lambda size_t k ; commentStarts(start, k));
  @*/

/*@ logic integer commentEnds(const char *c, size_t offset) =
  @   ('\0' == start[offset] || '\0' == start[offset+1]) ? 0
  @   : (('*'==start[offset] && ')' == start[offset+1]) ? 1 : 0);
  @*/

/*@ logic integer numOfCommentEnds(const char *start, size_t length) =
  @   \numof(0, length, \lambda size_t k ; commentEnds(start, k));
  @*/

/*@ logic boolean hasBalancedComments(const char *str) =
  @   numOfCommentStarts(str, \strlen(str)) <= numOfCommentEnds(str, \strlen(str));
  @*/

/* Caveat: for runaway comments, it DOES NOT skip it. Instead, it sets
 * `this->current` to be the end of the string, and returns a
 * `SKIP_COMMENT_RUNAWAY` status to indicate the scanner has, well, found
 * a bug.
 */
/*@ requires \valid(this);
  @ behavior skip_comment:
  @   assumes !isCommentStart(this);
  @   ensures SKIP_COMMENT_NONE_FOUND == \result;
  @ behavior runaway_comment:
  @   assumes isCommentStart(this);
  @   assumes !hasBalancedComments(this->current);
  @   ensures this->current == \old(this)->current;
  @   ensures SKIP_COMMENT_RUNAWAY == \result;
  @ behavior default:
  @   assumes isCommentStart(this);
  @   assumes hasBalancedComments(this->current);
  @   assigns this->current;
  @   ensures SKIP_COMMENT_SUCCESS == \result;
  @ disjoint behaviors;
  @ complete behaviors;
  @*/
static enum SKIP_COMMENT_STATUS skipComment(mml_Scanner *this) {
    if (!isCommentStart(this)) return SKIP_COMMENT_NONE_FOUND;
    //@ assert isCommentStart(this)
    
    enum SKIP_COMMENT_STATUS status;
    size_t depth = 1;
    size_t line = this->line;
    const char *current = this->current;
    advance(this); // consume '('
    advance(this); // consume '*'
    //@ assert (this->current) > current;
    //@ assert !isCommentStart(this) && 1 == depth;
    /*@ assert depth > 0; */ // in particular...
    
    // eat everything in the block comment until corresponding "*)"
    //@ assert (this->current) > current;
    //@ invariant depth == numOfCommentStarts(current, this->current - current) - numOfCommentEnds(current, this->current - current);
    while (depth > 0 && mml_Scanner_hasNext(this)) {
        //@ assert depth > 0
        depth = adjustCommentDepth(this, depth);
        //@ assert depth >= 0
        advance(this);
        //@ assert (this->current) > current;
    }
    //@ assert (this->current) > current;
    //@ assert depth == 0 || !mml_Scanner_hasNext(this);
    if (depth > 0) {
        // handle runaway comments
        //@ assert !mml_Scanner_hasNext(this);
        //@ assert numOfCommentStarts(current, strlen(current)) > numOfCommentEnds(current, strlen(current));
        //@ assert !hasBalancedComments(current);
        status = SKIP_COMMENT_RUNAWAY;
        // reset the scanner
        this->current = current;
        //@ assert (this->current) == current;
        this->line = line;
    } else {
        //@ assert depth == 0 && mml_Scanner_hasNext(this);
        //@ assert (this->current) > current;
        //@ assert numOfCommentStarts(current, (size_t)(this->current - current)) == numOfCommentEnds(current, (size_t)(this->current - current));
        //@ assert hasBalancedComments(current);
        status = SKIP_COMMENT_SUCCESS;
        //@ assert (this->current) > current;
    }
    return status;
}

/*@ requires \valid(this);
  @ ensures \forall size_t c; 0 <= c < (size_t)(this->current - (\old(this->current)))
  @          ==> isspace(\old(this)->current[c]);
  @ ensures \result == (\old(this)->current != this->current);
  @*/
static bool skipWhitespace(mml_Scanner *this) {
    bool hasSkippedWS = isspace(peek(this));
    const char *current = this->current;
    //@ assert current == \old(this->current);
    //@ assert current <= this->current;
    //@ loop invariant for c in (current..this->current), isspace(c);
    while (isspace(peek(this))) {
        if ('\n' == peek(this)) {
            this->line += 1;
        }
        advance(this);
        //@ assert current < this->current;
    }
    //@ assert current <= this->current;
    return hasSkippedWS;
}

/* For runaway comments, it skips the leading whitespace, but NOT the comment
 * start. So if the `result->start` starts with "(*", then AND ONLY THEN
 * is the scanner experiencing a runaway comment.
 */
/*@ requires \valid(this);
  @ behavior does_nothing:
  @   assumes !isspace(peek(\old(this))) && !isCommentStart(\old(this));
  @ behavior default:
  @   assumes isspace(peek(\old(this))) || isCommentStart(\old(this));
  @   assigns this->current;
  @   ensures isCommentStart(this) || (!isCommentStart(this) && !isspace(peek(this)));
  @ complete behaviors;
  @ disjoint behaviors;
  @*/
static void skipWhitespaceAndComments(mml_Scanner *this) {
    bool hasSkippedWhitespace;
    enum SKIP_COMMENT_STATUS status;
    do {
        hasSkippedWhitespace = skipWhitespace(this);
        status = skipComment(this);
    } while (hasSkippedWhitespace || SKIP_COMMENT_SUCCESS == status);
    // `this->start` looks like "(*" iff experiencing a runaway comment
}

/*@ requires \valid(this);
  @ allocates *token;
  @ assigns \result;
  @ ensures \valid(\result);
  @ ensures type == mml_Token_type(\result);
  @ ensures (size_t)((this->current) - (this->start)) == mml_Token_length(\result);
  @ ensures this->start == \result->start;
  @*/
static mml_Token* makeToken(mml_Scanner *this, MML_TokenType type) {
    size_t length = (size_t)((this->current) - (this->start));
    mml_Token *token = mml_Token_new(type, this->start, length, this->line);
    return token;
}

/*@ requires \valid(scanner);
  @ requires \valid(keyword);
  @ behavior matches_keyword:
  @   assumes (size_t)((scanner->current) - (scanner->start)) == start + length;
  @   assumes 0 == memcmp(scanner->start + start, keyword, length);
  @   ensures type == \result;
  @ behavior default:
  @   assumes !(((size_t)((scanner->current) - (scanner->start)) == start + length)
  @    && (0 == memcmp(scanner->start + start, keyword, length)));
  @   ensures MML_TOKEN_IDENTIFIER == \result;
  @ disjoint behaviors;
  @ complete behaviors;
  @*/
  static MML_TokenType matchKeyword(mml_Scanner *scanner,
                                  size_t start,
                                  size_t length,
                                  const char *keyword,
                                  MML_TokenType type) {
    if ((size_t)((scanner->current) - (scanner->start)) == start + length
        && 0 == memcmp(scanner->start + start, keyword, length)) {
        return type;
    }
    return MML_TOKEN_IDENTIFIER;
}

// See https://www.haskell.org/onlinereport/lexemes.html
/*@ ensures isalnum(c) || '\'' == c || '_' == c;
  @*/
static bool isIdentifierChar(char c) {
    return (isalnum(c) || ('\'' == c) || ('_' == c));
}

/*@ requires \valid(scanner);
  @ assigns scanner->current;
  @ ensures (scanner->current) > (scanner->start);
  @ ensures (MML_TOKEN_KW_START < \result && result < MML_TOKEN_KW_END)
  @         || (MML_TOKEN_IDENTIFIER == \result);
  @*/
static MML_TokenType scanIdOrKeyword(mml_Scanner *scanner) {
    while (isIdentifierChar(peek(scanner)))
        advance(scanner);
    // matches "fn", "if", "then", "else", "True", "False", etc.
    switch (scanner->start[0]) {
    case 'c':
        return matchKeyword(scanner, 1, 3, "ase", MML_TOKEN_CASE);
    case 'd':
        return matchKeyword(scanner, 1, 3, "ata", MML_TOKEN_DATA);
    case 'e':
        return matchKeyword(scanner, 1, 3, "lse", MML_TOKEN_ELSE);
    case 'f':
        if (6 == scanner->current - scanner->start) {
            return matchKeyword(scanner, 1, 5, "orall", MML_TOKEN_FORALL);
        } else {
            return matchKeyword(scanner, 1, 1, "n", MML_TOKEN_FN);
        }
        break;
    case 'i':
        if (scanner->current - scanner->start > 1) {
            if ('f' == scanner->start[1]) {
                return matchKeyword(scanner, 1, 1, "f", MML_TOKEN_IF);
            } else if ('n' == scanner->start[1]) {
                return matchKeyword(scanner, 1, 1, "n", MML_TOKEN_IN);
            }
        }
        break;
    case 'l':
        if (scanner->current - scanner->start > 2) {
            if (('e' == scanner->start[1]) && ('t' == scanner->start[2])) {
                if (3 == scanner->current - scanner->start) {
                    return matchKeyword(scanner, 1, 2, "et", MML_TOKEN_LET);
                } else {
                    return matchKeyword(scanner, 1, 5, "etrec", MML_TOKEN_LETREC);
                }
            }
        }
        break;
    case 'n':
        return matchKeyword(scanner, 1, 6, "ewtype", MML_TOKEN_NEWTYPE);  
    case 'o':
        return matchKeyword(scanner, 1, 1, "f", MML_TOKEN_OF);
    case 't':
        return matchKeyword(scanner, 1, 3, "hen", MML_TOKEN_THEN);
    case 'B':
        return matchKeyword(scanner, 1, 3, "ool", MML_TOKEN_BOOL);
    case 'F':
        return matchKeyword(scanner, 1, 4, "alse", MML_TOKEN_FALSE);
    case 'I':
        return matchKeyword(scanner, 1, 2, "nt", MML_TOKEN_INT); 
    case 'T':
        return matchKeyword(scanner, 1, 3, "rue", MML_TOKEN_TRUE);
    default:
        break;
    }
    return MML_TOKEN_IDENTIFIER;
}

/*@ logic size_t indexOfLastDigit(const char *c) =
  @   isdigit(c[0]) ? 1 + indexOfLastDigit(c++) : ('\0' == c[0] ? 0 : 1);
  @*/

// TODO floating point numbers, for now I'm skipping them
// TODO handle scientific notation, "3e5"
/*@ requires \valid(scanner);
  @ requires isdigit(scanner->current[0])
  @          || ('-' == scanner->current[0] && isdigit(scanner->current[1]));
  @ behavior default:
  @   assumes !isalpha(scanner->current[indexOfLastDigit(scanner->current)]);
  @   ensures mml_Token_isNumber(\result);
  @ behavior bad_format:
  @   assumes isalpha(scanner->current[indexOfLastDigit(scanner->current)]);
  @   ensures mml_Token_isError(\result);
  @ disjoint behaviors;
  @ complete behaviors;
  @*/
static mml_Token* scanNumber(mml_Scanner *scanner) {
    //@ assert isdigit(peek(scanner));
    while (isdigit(peek(scanner))) advance(scanner);
    //@ assert !isdigit(peek(scanner));

    mml_Token *token;
    // so "302a" is an error, but "302+" is two tokens "302" and "+"
    if (!mml_Scanner_hasNext(scanner) || !isalpha(peek(scanner))) {
        token = makeToken(scanner, MML_TOKEN_INTEGER);
        //@ assert mml_Token_isNumber(token);
    } else {
        //@ assert scanner_hasNext(scanner)
        //@ assert isalpha(peek(scanner))
        
        /* e.g., "1foo" is a token error */
        while (mml_Scanner_hasNext(scanner) && isalnum(peek(scanner))) {
            advance(scanner);
        }
        //@ assert (!mml_Scanner_hasNext(scanner) || !isalpha(peek(scanner)));
        token = makeToken(scanner, MML_TOKEN_ERROR);
        //@ assert mml_Token_isError(token);
    }
    //@ assert (!mml_Scanner_hasNext(scanner) || !isalpha(peek(scanner)))
    //@ assert mml_Token_isError(token) || mml_Token_isNumber(token);
    return token;
}

static mml_Token* scanString(mml_Scanner *scanner) {
    assert('"' == scanner->current[-1]);
    //@ assert '"' == scanner->current[-1];
    mml_Token *token;
    size_t line = scanner->line;
    
    while ('"' != peek(scanner) && mml_Scanner_hasNext(scanner)) {
        if ('\n' == peek(scanner)) {
            scanner->line++;
        } else if ('\\' == peek(scanner) && '"' == peekNext(scanner)) {
            // TODO: handle other escaped characters?
            advance(scanner);
        }
        advance(scanner);
    }
    //@ assert ('"' == peek(scanner)) || !mml_Scanner_hasNext(scanner);
    
    if (!mml_Scanner_hasNext(scanner)) {
        // unterminated string
        token = makeToken(scanner, MML_TOKEN_ERROR);
        mml_Token_setLine(token, line);
        //@ assert mml_Token_isError(token);
    } else {
        //@ assert ('"' == peek(scanner));
        advance(scanner); // the closing '"' char
        token = makeToken(scanner, MML_TOKEN_STRING);
        //@ assert mml_Token_isString(token);
    }
    //@ assert mml_Token_isError(token) || mml_Token_isString(token);
    return token;
}

/*@ requires \valid(scanner);
  @ allocates \result;
  @ assigns \result;
  @ ensures mml_Token_isSymbol(\result) || mml_Token_isError(\result);
  @*/
static mml_Token* scanSymbol(mml_Scanner *scanner) {
    char c = scanner->current[-1];
    mml_Token *token;
    switch (c) {
    case '"':
        token = scanString(scanner);
        //@ assert mml_Token_isSymbol(token);
        break;
    case '(':
        token = makeToken(scanner, MML_TOKEN_LEFT_PAREN);
        //@ assert mml_Token_isSymbol(token);
        break;
    case ')':
        token = makeToken(scanner, MML_TOKEN_RIGHT_PAREN);
        //@ assert mml_Token_isSymbol(token);
        break;
    case '*':
        token = makeToken(scanner, MML_TOKEN_STAR);
        //@ assert mml_Token_isSymbol(token);
        break;
    case '+':
        token = makeToken(scanner, MML_TOKEN_PLUS);
        //@ assert mml_Token_isSymbol(token);
        break;
    case '-':
        if ('>' == peek(scanner)) {
            advance(scanner);
            token = makeToken(scanner, MML_TOKEN_FN_ARROW);
        } else {
            token = makeToken(scanner, MML_TOKEN_MINUS);
        }
        //@ assert mml_Token_isSymbol(token);
        break;
    case ':':
        if (':' == peek(scanner)) {
            advance(scanner);
            token = makeToken(scanner, MML_TOKEN_ESTI);
        } else {
            token = makeToken(scanner, MML_TOKEN_COLON);
        }
        //@ assert mml_Token_isSymbol(token);
        break;
    case ';':
        token = makeToken(scanner, MML_TOKEN_SEMICOLON);
        //@ assert mml_Token_isSymbol(token);
        break;
    case '=':
        token = makeToken(scanner, MML_TOKEN_EQUAL);
        //@ assert mml_Token_isSymbol(token);
        break;
    case '@':
        token = makeToken(scanner, MML_TOKEN_AT_SIGN);
        //@ assert mml_Token_isSymbol(token);
        break;
    case '_':
        token = makeToken(scanner, MML_TOKEN_UNDERSCORE);
        //@ assert mml_Token_isSymbol(token);
        break;
    case '{':
        token = makeToken(scanner, MML_TOKEN_LEFT_BRACE);
        //@ assert mml_Token_isSymbol(token);
        break;
    case '}':
        token = makeToken(scanner, MML_TOKEN_RIGHT_BRACE);
        //@ assert mml_Token_isSymbol(token);
        break;
    default:
        // scanner->start[0] is one of these:  ?<>'[]!#$%^&`~
        // when all else fails, it's an error token
        token = makeToken(scanner, MML_TOKEN_ERROR);
        //@ assert mml_Token_isError(token);
        break;
    }
    //@ assert mml_Token_isSymbol(token) || mml_Token_isError(token);
    return token;
}

/*@ requires \valid(this);
  @ requires isCommentStart(this);
  @ requires this->start == this->current;
  @ ensures \valid(\result);
  @ ensures mml_Token_isError(\result);
  @ ensures mml_Token_length(\result) == strlen(this->start);
  @ ensures \result->start == this->start;
  @*/
static mml_Token* handleRunawayComment(mml_Scanner *this) {
    assert (isCommentStart(this)); // precondition
    // runaway comment!
    size_t length = strlen(this->start);
    this->current += length;
    return makeToken(this, MML_TOKEN_ERROR);
}

// TODO: figure this out
/*@ logic char firstCharAfterWhitespace(mml_Scanner *this) =
  @*/

/*@ requires \valid(this);
  @ allocates \result;
  @ assigns \result;
  @ behavior runaway_comment:
  @   assumes !isBalancedComments(this->current);
  @   ensures mml_Token_isError(\result);
  @ behavior scanner_has_no_next:
  @   assumes hasBalancedComments(this->current);
  @   assumes '\0' == firstCharAfterWhitespace(this);
  @   ensures mml_Token_isEOF(\result);
  @ behavior lexeme_starts_with_alpha:
  @   assumes hasBalancedComments(this->current);
  @   assumes isalpha(firstCharAfterWhitespace(this));
  @   ensures mml_Token_isIdentifier(\result) || mml_Token_isKeyword(\result);
  @ behavior lexeme_is_number:
  @   assumes isdigit(firstCharAfterWhitespace(this))
  @          ('-' == firstCharAfterWhitespace(this));
  @   ensures mml_Token_isNumber(\result) || mml_Token_isError(\result);
  @ behavior lexeme_is_symbol:
  @   assumes ispunct(firstCharAfterWhitespace(this));
  @   ensures mml_Token_isSymbol(\result) || mml_Token_isError(\result);
  @ disjoint behaviors;
  @ complete behaviors;
  @*/
mml_Token* mml_Scanner_next(mml_Scanner *this) {
    skipWhitespaceAndComments(this);
    //@ assert mml_Scanner_hasNext(this) ==> !isspace(this->current[0]);
    this->start = this->current;
    //@ assert mml_Scanner_hasNext(this) ==> !isspace(this->start[0]);
    //@ assert this->current >= this->start;

    mml_Token *token;
    if (!mml_Scanner_hasNext(this)) {
        token = makeToken(this, MML_TOKEN_EOF);
        //@ assert mml_Token_isEOF(token);
    } else if (isCommentStart(this)) {
        token = handleRunawayComment(this);
        //@ assert mml_Token_isError(token);
    } else {
        // default case
        char c = advance(this);
        if (isalpha(c)) {
            MML_TokenType type = scanIdOrKeyword(this);
            //@ assert type != MML_TOKEN_ERROR
            token = makeToken(this, type);
            //@ assert mml_Token_isIdentifier(token) || mml_Token_isKeyword(token)
        } else if (isdigit(c) || ('-' == c && isdigit(peek(this)))) {
            token = scanNumber(this);
            //@ assert mml_Token_isNumber(token) || mml_Token_isError(token)
        } else {
            //@ assert (!isalnum(c)) || ('-' == c && !isdigit(peek(this)))
            token = scanSymbol(this);
            //@ assert mml_Token_isSymbol(token) || mml_Token_isError(token)
        }
    }
    //@ assert NULL != token
    return token;
}
