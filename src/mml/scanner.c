#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <string.h> /* memcmp(), strnlen() */
#include "defs.h"
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

void mml_Scanner_free(mml_Scanner *this) {
    if (NULL == this) return;
    free(this);
    this = NULL;
}

static bool isWhitespace(char c) {
    return (c == ' ' || c == '\t' || c == '\r' || c == '\f' || c == '\n');
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
        if (!isWhitespace(this->current[c])) {
            hasNext = true;
        }
    }
    //@ assert ('\0' != this->current[c]) ==> !isWhitespace(this->current[c])
    return hasNext;
}

/* ******************************************************
   Everything else is just a helper to mml_Scanner_next()
*/
/*@ require \valid(this);
  @ ensures \result == this->current[0]
  @*/
static char peek(mml_Scanner *this) {
    assert(NULL != this);
    return this->current[0];
}

static char peekNext(mml_Scanner *this) {
    return (mml_Scanner_hasNext(this) ? this->current[1] : '\0');
}

/**
 * @return The current character the scanner is pointing at
 */
static char advance(mml_Scanner *this) {
    this->current++;
    return this->current[-1];
}

static bool isCommentStart(mml_Scanner *this) {
    return (('(' == peek(this)) && ('*' == peekNext(this)));
}

static enum SKIP_COMMENT_STATUS {
    SKIP_COMMENT_SUCCESS = 0,
    SKIP_COMMENT_RUNAWAY,
    SKIP_COMMENT_NONE_FOUND
};

static enum SKIP_COMMENT_STATUS skipComment(mml_Scanner *this) {
    if (!isCommentStart(this)) return SKIP_COMMENT_SUCCESS;

    // assert "(*" is this->current[0:1]
    enum SKIP_COMMENT_STATUS status;
    size_t depth = 1;
    const char *start = this->current;
    advance(this);
    advance(this);
    /* a block comment until next "*)" */
    while (depth > 0 && mml_Scanner_hasNext(this)) {
        if ('\n' == peek(this)) {
            this->line += 1;
        } else if ('(' == peek(this) && '*' == peekNext(this)) {
            depth += 1;
            advance(this);
        } else if ('*' == peek(this) && ')' == peekNext(this)) {
            // assert (depth > 0)
            depth -= 1;
            // assert (depth >= 0)
            advance(this);
        }
        advance(this);
    }
    //@ assert mml_Scanner_hasNext(this) ==> (0 == depth)
    if (depth > 0 && !mml_Scanner_hasNext(this)) {
        // handle runaway comments
        // static const char *suffix = ;
        status = SKIP_COMMENT_RUNAWAY;
        this->current = start; // set current to point to the start of
                               // the runaway
    } else {
        status = SKIP_COMMENT_SUCCESS;
    }
    return status;
}

/**
 * Have a scanner skip over whitespace.
 *
 * If the given @c mml_Scanner object's current pointer is currently at a
 * whitespace character, then update it to point at the first non-whitespace
 * character. Otherwise, do not mutate the object.
 *
 * Returns @c true if and only if the @c mml_Scanner object has been mutated.
 * 
 * @param this A valid @c mml_Scanner which will skip over whitespace.
 * @returns @c true if any amount of whitespace has been skipped, @c false otherwise.
 */
static bool skipWhitespace(mml_Scanner *this) {
    bool finished = false;
    bool hasSkippedWS = false;
    while (!finished) {
        char c = peek(this);
        switch(c) {
        case ' ':
        case '\f':
        case '\r':
        case '\t':
            advance(this);
            hasSkippedWS = true;
            break;
        case '\n':
            this->line += 1;
            advance(this);
            hasSkippedWS = true;
            break;
        default:
            finished = true;
            break;
        }
    }
    return hasSkippedWS;
}

static void skipWhitespaceAndComments(mml_Scanner *this) {
    bool finished = false;
    bool hasSkippedWhitespace = false;
    enum SKIP_COMMENT_STATUS status;
    while (!finished) {
        status = SKIP_COMMENT_NONE_FOUND;
        hasSkippedWhitespace = skipWhitespace(this);
        if (isCommentStart(this)) {
            status = skipComment(this);
        }
        // isFinished = !hasSkippedWhitespace && SKIP_COMMENT_NONE == status
        finished = !hasSkippedWhitespace && (SKIP_COMMENT_SUCCESS != status);
    }
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

/*@ lemma partition_of_printable_char:
  @ \forall char c ;
  @    isPrintable(c) ==> isAlphaNumeric(c) ^^ isPunctuation(c) ^^ (c == ' ') ;
  @*/
/*@ lemma partition_of_char:
  @  \forall char c ;
  @      isControl(c) ^^ isPrintable(c) ;
  @*/
static bool isControl(char c) {
    return (c < ' ') || (c == 127);
}

static bool isPrintable(char c) {
    return !isControl(c);
}

static bool isDigit(char c) {
    return '0' <= c && c <= '9';
}

static bool isLowerCase(char c) {
    return 'a' <= c && c <= 'z';
}

static bool isUpperCase(char c) {
    return 'A' <= c && c <= 'Z';
}

static bool isAlpha(char c) {
    return isLowerCase(c) || isUpperCase(c);
}

static bool isAlphaNumeric(char c) {
    return isAlpha(c) || isDigit(c);
}

static bool isPunctuation(char c) {
    return ('!' <= c && c <= '/') || (':' <= c && c <= '@')
        || ('[' <= c && c <= '`') || ('{' <= c && c <= '~');
}

/**
 * Following Haskell, allow alphanumerics, apostrophes, and underscores
 * for identifiers.
 *
 * @see https://www.haskell.org/onlinereport/lexemes.html
 */
static bool isIdentifierChar(char c) {
    return (isAlphaNumeric(c) || ('\'' == c) || ('_' == c));
}

/**
 * @pre <code>(scanner->current) == (scanner->start)</code>
 * @post @c scanner->current is after @c scanner->start
 */
static MML_TokenType scanLexeme(mml_Scanner *scanner) {
    while (isIdentifierChar(peek(scanner)))
        advance(scanner);
    // matches "fn", "if", "then", "else", "True", "False"
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
    while (isDigit(peek(scanner))) advance(scanner);
    /*@ assert !isDigit(peek(scanner)) */

    mml_Token *token;
    /* TODO floating point numbers, for now I'm skipping them */
    // so "302a" is an error, but "302+" is not
    if (!mml_Scanner_hasNext(scanner) || !isAlpha(peek(scanner))) {
        token = makeToken(scanner, MML_TOKEN_INTEGER);
    } else {
        //@ assert scanner_hasNext(scanner)
        //@ assert isAlpha(peek(scanner))
        /* e.g., "1foo" is a token error */
        while (mml_Scanner_hasNext(scanner) && isAlphaNumeric(peek(scanner)))
            advance(scanner);
        token = makeToken(scanner, MML_TOKEN_ERROR);
    }
    /*@ assert mml_Token_isError(token) || mml_Token_isNumber(token) */
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
    case '{':
        token = makeToken(scanner, MML_TOKEN_LEFT_BRACE);
        break;
    case '}':
        token = makeToken(scanner, MML_TOKEN_RIGHT_BRACE);
        break;
    case '(':
        token = makeToken(scanner, MML_TOKEN_LEFT_PAREN);
        break;
    case ')':
        token = makeToken(scanner, MML_TOKEN_RIGHT_PAREN);
        break;
    case ';':
        token = makeToken(scanner, MML_TOKEN_SEMICOLON);
        break;
    case '*':
        token = makeToken(scanner, MML_TOKEN_STAR);
        break;
    case ':':
        if (':' == peek(scanner)) {
            advance(scanner);
            token = makeToken(scanner, MML_TOKEN_ESTI);
        } else {
            token = makeToken(scanner, MML_TOKEN_COLON);
        }
        break;
    case '-':
        if ('>' == peek(scanner)) {
            advance(scanner);
            token = makeToken(scanner, MML_TOKEN_FN_ARROW);
        } else {
            token = makeToken(scanner, MML_TOKEN_MINUS);
        }
        break;
    case '=':
        token = makeToken(scanner, MML_TOKEN_EQUAL);
        break;
    case '+':
        token = makeToken(scanner, MML_TOKEN_PLUS);
        break;
    default:
        /* scanner->start[0] is one of these:  ?<>:;"'[{]}!@#$%^&_`~    */
        /* when all else fails, it's an error token */
        token = makeToken(scanner, MML_TOKEN_ERROR);
        break;
    }
    /*@ assert mml_Token_isSymbol(token) || mml_Token_isError(token) */
    return token;
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
        // runaway comment!
        size_t length = strlen(this->start);
        this->current += length;
        token = makeToken(this, MML_TOKEN_ERROR);
    } else {
        // default case
        char c = advance(this);
        if (isAlpha(c)) {
            MML_TokenType type = scanLexeme(this);
            /*@ assert type != MML_TOKEN_ERROR */
            token = makeToken(this, type);
            /*@ assert mml_Token_isIdentifier(token) || mml_Token_isKeyword(token) */
        } else if (isDigit(c) || ('-' == c && isDigit(peek(this)))) {
            token = scanNumber(this);
        } else {
            /*@ assert (!isAlphaNumeric(c)) */
            token = scanSymbol(this);
            /*@ assert mml_Token_isSymbol(token) || mml_Token_isError(token) */
        }
    }
    // assert NULL != token
    return token;
}