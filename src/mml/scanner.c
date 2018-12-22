#include <ctype.h>
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <string.h> /* memcmp(), strnlen() */
#include "utils.h"
#include "mml/token.h"
#include "mml/scanner.h"

/**
 * Constructs scanner for input buffer.
 *
 * Constructs a new @c mml_Scanner that produces @c mml_Token values
 * from the specified input source.
 *
 * @param source An input stream to be scanned.
 */
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

/**
 * Free @c mml_Scanner object.
 *
 * This frees the memory allocated for @c this mml_Scanner object, but
 * @em not for the input stream. Why? Because we might have lingering
 * mml_Token objects still referencing the input stream.
 *
 * @param this The mml_Scanner object to be freed.
 * @return nothing
 */
void mml_Scanner_free(mml_Scanner *this) {
    if (NULL == this) return;
    free(this);
    this = NULL;
}


/**
 * Returns @c true if this scanner has another token in its input.
 *
 * When the scanner is at the end, it returns only @c false.
 * 
 * @param this The mml_Scanner object being inspected
 * @return true if the scanner has another token
 */
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

/* ******************************************************
   Everything else is just a helper to mml_Scanner_next()
*/
/*@ require \valid(this);
  @ ensures \result == this->current[0]
  @*/
static char peek(mml_Scanner *this) {
    if (NULL == this) return '\0';
    return this->current[0];
}

static char peekNext(mml_Scanner *this) {
    return (mml_Scanner_hasNext(this) ? this->current[1] : '\0');
}

static char advance(mml_Scanner *this) {
    if (NULL == this) return '\0';
    this->current++;
    return this->current[-1];
}

static bool isCommentStart(mml_Scanner *this) {
    return (('(' == peek(this)) && ('*' == peekNext(this)));
}

static bool isCommentEnd(mml_Scanner *this) {
    return (('*' == peek(this)) && (')' == peekNext(this)));
}

enum SKIP_COMMENT_STATUS {
    SKIP_COMMENT_SUCCESS = 0,
    SKIP_COMMENT_RUNAWAY,
    SKIP_COMMENT_NONE_FOUND
};

/*@ requires \valid(this);
  @ behavior newline:
  @     assumes '\n' == peek(\old(this));
  @     assigns this->line;
  @     ensures this->line == 1 + \old(this->line);
  @     ensures \result == depth;
  @ behavior increase_depth:
  @     assumes isCommentStart(\old(this));
  @     assigns this->current;
  @     ensures \result == depth + 1;
  @     ensures !isCommentStart(this);
  @ behavior decrease_depth:
  @     assumes isCommentEnd(\old(this));
  @     assigns this->current;
  @     ansures \result == depth - 1;
  @     ensures !isCommentEnd(this);
  @ behavior default_behavior:
  @     assumes !isCommentStart(\old(this));
  @     assumes !isCommentEnd(\old(this));
  @     assumes '\n' != peek(\old(this));
  @     ensures \result == depth;
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

static size_t commentStartIndicator(const char *start, size_t offset) {
    if ('(' == start[offset] && '*' == start[offset+1]) {
        return 1;
    } else {
        return 0;
    }
}

/*@ logic integer commentStarts(const char *c, size_t offset) =
  @   ('('==start[offset] && '*' == start[offset+1]) ? 1 : 0 ;
  @*/
/*@ logic integer numOfCommentStarts(const char *start, size_t length) =
  @   \numof(0, length, \lambda size_t k ; commentStarts(start, k));
  @*/
/*@ requires \valid(start) && \valid(end);
  @ behavior exception:
  @   assumes start >= end;
  @   ensures 0 == \result;
  @ behavior default:
  @   assumes start < end;
  @   ensures \result == numOfCommentStarts(start, (size_t)(end - start));
  @ disjoint behaviors;
  @ complete behaviors;
  @*/
static size_t countCommentStarts(const char *start, const char *end) {
    if (start >= end) return 0;
    size_t counter = 0;
    size_t length = (size_t)(end - start);
    //@ loop invariant counter == numOfCommentStarts(start, c);
    for (size_t c = 0; length > c; c++) {
        if ('('==start[c] && '*' == start[c+1]) {
            counter = counter + 1;
            c++;
        }
    }
    return counter;
}


/*@ logic integer commentEnds(const char *c, size_t offset) =
  @   ('*'==start[offset] && ')' == start[offset+1]) ? 1 : 0 ;
  @*/
/*@ logic integer numOfCommentEnds(const char *start, size_t length) =
  @   \numof(0, length, \lambda size_t k ; commentEnds(start, k));
  @*/
/*@ requires \valid(start) && \valid(end);
  @ behavior exception:
  @   assumes start >= end;
  @   ensures 0 == \result;
  @ behavior default:
  @   assumes start < end;
  @   ensures \result == numOfCommentEnds(start, (size_t)(end - start));
  @ disjoint behaviors;
  @ complete behaviors;
  @*/
static size_t countCommentEnds(const char *start, const char *end) {
    if (start >= end) return 0;
    size_t counter = 0;
    size_t length = (size_t)(end - start);
    //@ loop invariant counter == numOfCommentEnds(start, c);
    for (size_t c = 0; length > c; c++) {
        if ('*'==start[c] && ')' == start[c+1]) {
            counter = counter + 1;
            c++;
        }
    }
    return counter;
}

/*@ requires \valid(str);
  @ ensures \result == (numOfCommentStarts(str, strlen(str)) <= numOfCommendEnds(str, strlen(str)));
  @*/
static bool hasBalancedComments(const char *str) {
    size_t len = strlen(str) + 1;
    return countCommentStarts(str, str + len) <= countCommentEnds(str, str + len);
}

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
    //@ assert !isCommentStart(this) && 1 == depth
    
    // eat everything in the block comment until corresponding "*)"
    //@ invariant depth == countCommentStarts(current, this->current) - countCommentEnds(current, this->current)
    for (; depth > 0 && mml_Scanner_hasNext(this); advance(this)) {
        depth = adjustCommentDepth(this, depth);
    }
    
    if (depth > 0) {
        //@ assert countCommentStarts(current, this->current) > countCommentEnds(current, this->current)
        //@ assert !hasBalancedComments(current);
        // handle runaway comments
        status = SKIP_COMMENT_RUNAWAY;
        // reset the scanner
        this->current = current;
        this->line = line;
    } else {
        //@ assert countCommentStarts(current, this->current) == countCommentEnds(current, this->current)
        //@ assert hasBalancedComments(current);
        status = SKIP_COMMENT_SUCCESS;
    }
    return status;
}
/*@ requires \valid(this);
  @ ensures for c in (\old(this)->current..this->current), isspace(c);
  @ ensures \result == (\old(this)->current != this->current);
  @*/
static bool skipWhitespace(mml_Scanner *this) {
    bool hasSkippedWS = isspace(peek(this));

    //@ loop invariant for c in (current..this->current), isspace(c);
    while (isspace(peek(this))) {
        if ('\n' == peek(this)) {
            this->line += 1;
        }
        advance(this);
    }
    return hasSkippedWS;
}

/* For runaway comments, it skips the leading whitespace, but NOT the comment
 * start. So if the `result->start` starts with "(*", then AND ONLY THEN
 * is the scanner experiencing a runaway comment.
 */
/*@ requires \valid(this);
  @ behavior does_nothing:
  @     assumes !isspace(peek(\old(this))) && !isCommentStart(\old(this));
  @ behavior default:
  @     assumes isspace(peek(\old(this))) || isCommentStart(\old(this));
  @     assigns this->current;
  @     ensures isCommentStart(this) || (!isCommentStart(this) && !isspace(peek(this)));
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

static mml_Token* makeToken(mml_Scanner *this, MML_TokenType type) {
    size_t length = (size_t)((this->current) - (this->start));
    mml_Token *token = mml_Token_new(type, this->start, length, this->line);
    return token;
}

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
static bool isIdentifierChar(char c) {
    return (isalnum(c) || ('\'' == c) || ('_' == c));
}

/**
 * Scan the next token for an identifier or reserved keyword.
 *
 * Given that the scanner is pointing at a letter character, the scanner
 * produces the appropriate reserved keyword or an identifier token type.
 * 
 * @pre <code>(scanner->current) == (scanner->start)</code>
 * @post @c scanner->current is after @c scanner->start
 */
static MML_TokenType scanLexeme(mml_Scanner *scanner) {
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

static mml_Token* scanNumber(mml_Scanner *scanner) {
    while (isdigit(peek(scanner))) advance(scanner);
    //@ assert !isdigit(peek(scanner))

    mml_Token *token;
    /* TODO floating point numbers, for now I'm skipping them */
    // so "302a" is an error, but "302+" is two tokens "302" and "+"
    if (!mml_Scanner_hasNext(scanner) || !isalpha(peek(scanner))) {
        token = makeToken(scanner, MML_TOKEN_INTEGER);
    } else {
        //@ assert scanner_hasNext(scanner)
        //@ assert isalpha(peek(scanner))
        /* e.g., "1foo" is a token error */
        while (mml_Scanner_hasNext(scanner) && isalnum(peek(scanner)))
            advance(scanner);
        token = makeToken(scanner, MML_TOKEN_ERROR);
    }
    //@ assert mml_Token_isError(token) || mml_Token_isNumber(token)
    return token;
}

static mml_Token* scanString(mml_Scanner *scanner) {
    assert('"' == scanner->current[-1]);
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
    
    if (!mml_Scanner_hasNext(scanner)) {
        // unterminated string
        token = makeToken(scanner, MML_TOKEN_ERROR);
        mml_Token_setLine(token, line);
    } else {
        advance(scanner); // the closing '"' char
        token = makeToken(scanner, MML_TOKEN_STRING);
    }
    return token;
}

static mml_Token* scanSymbol(mml_Scanner *scanner) {
    char c = scanner->current[-1];
    mml_Token *token;
    switch (c) {
    case '"':
        token = scanString(scanner);
        break;
    case '(':
        token = makeToken(scanner, MML_TOKEN_LEFT_PAREN);
        break;
    case ')':
        token = makeToken(scanner, MML_TOKEN_RIGHT_PAREN);
        break;
    case '*':
        token = makeToken(scanner, MML_TOKEN_STAR);
        break;
    case '+':
        token = makeToken(scanner, MML_TOKEN_PLUS);
        break;
    case '-':
        if ('>' == peek(scanner)) {
            advance(scanner);
            token = makeToken(scanner, MML_TOKEN_FN_ARROW);
        } else {
            token = makeToken(scanner, MML_TOKEN_MINUS);
        }
        break;
    case ':':
        if (':' == peek(scanner)) {
            advance(scanner);
            token = makeToken(scanner, MML_TOKEN_ESTI);
        } else {
            token = makeToken(scanner, MML_TOKEN_COLON);
        }
        break;
    case ';':
        token = makeToken(scanner, MML_TOKEN_SEMICOLON);
        break;
    case '=':
        token = makeToken(scanner, MML_TOKEN_EQUAL);
        break;
    case '@':
        token = makeToken(scanner, MML_TOKEN_AT_SIGN);
        break;
    case '_':
        token = makeToken(scanner, MML_TOKEN_UNDERSCORE);
        break;
    case '{':
        token = makeToken(scanner, MML_TOKEN_LEFT_BRACE);
        break;
    case '}':
        token = makeToken(scanner, MML_TOKEN_RIGHT_BRACE);
        break;
    default:
        // scanner->start[0] is one of these:  ?<>'[]!#$%^&`~
        // when all else fails, it's an error token
        token = makeToken(scanner, MML_TOKEN_ERROR);
        break;
    }
    //@ assert mml_Token_isSymbol(token) || mml_Token_isError(token)
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

/**
 * Produce the next token on demand.
 *
 * Finds and returns the next token from the scanner. When the scanner has
 * "finished", it will only produce EOF tokens.
 *
 * @param this The mml_Scanner object in question.
 * @return A pointer to the next mml_Token object.
 * @pre @c this is a valid pointer to a mml_Scanner object.
 */
mml_Token* mml_Scanner_next(mml_Scanner *this) {
    skipWhitespaceAndComments(this);
    this->start = this->current;

    mml_Token *token;
    if (!mml_Scanner_hasNext(this)) {
        token = makeToken(this, MML_TOKEN_EOF);
    } else if (isCommentStart(this)) {
        token = handleRunawayComment(this);
    } else {
        // default case
        char c = advance(this);
        if (isalpha(c)) {
            MML_TokenType type = scanLexeme(this);
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
