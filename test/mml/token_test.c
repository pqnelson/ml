#include <stdlib.h>
#include <stdio.h>
#include <stddef.h>
#include <string.h> /* strlen() */
#include "utils.h"
#include "mml/token.h"
#include "test.h"
#include "testsuites.h"

static void TokenLexemeEqualsTest1(TestCase *this) {
    const char *lexeme = "foobar";
    mml_Token *token = mml_Token_new(MML_TOKEN_IDENTIFIER,
                                     lexeme,
                                     strlen(lexeme),
                                     1);
    assertTrue(mml_Token_lexemeEquals(token, lexeme));
    mml_Token_free(token);
}

static void TokenLexemeEqualsTest2(TestCase *this) {
    const char *lexeme = "foobar";
    const char *comparedLexeme = "foo";
    mml_Token *token = mml_Token_new(MML_TOKEN_IDENTIFIER,
                                     lexeme,
                                     strlen(lexeme),
                                     1);
    assertFalse(mml_Token_lexemeEquals(token, comparedLexeme));
    mml_Token_free(token);
}

static void TokenLexemeEqualsTest3(TestCase *this) {
    const char *lexeme = "foo";
    const char *comparedLexeme = "foobar";
    mml_Token *token = mml_Token_new(MML_TOKEN_IDENTIFIER,
                                     lexeme,
                                     strlen(lexeme),
                                     1);
    assertFalse(mml_Token_lexemeEquals(token, comparedLexeme));
    mml_Token_free(token);
}

#ifdef add_test
#undef add_test
#endif
#define add_test(name) TestSuite_addTest(currentSuite, test(name))

void initTokenSuite() {
    TestSuite* currentSuite;
    suite(currentSuite);
    
    add_test(TokenLexemeEqualsTest1);
    add_test(TokenLexemeEqualsTest2);
    add_test(TokenLexemeEqualsTest3);
}
#undef add_test
