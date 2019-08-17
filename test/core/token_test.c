#include <stdlib.h>
#include <stdio.h>
#include <stddef.h>
#include <string.h> /* strlen() */
#include "utils.h"
#include "core/token.h"
#include "test.h"
#include "testsuites.h"

static void TokenLexemeEqualsTest1(TestCase *this) {
    const char *lexeme = "foobar";
    core_Token *token = core_Token_new(CORE_TOKEN_IDENTIFIER,
                                     lexeme,
                                     strlen(lexeme),
                                     1);
    assertTrue(core_Token_lexemeEquals(token, lexeme));
    core_Token_free(token);
}

static void TokenLexemeEqualsTest2(TestCase *this) {
    const char *lexeme = "foobar";
    const char *comparedLexeme = "foo";
    core_Token *token = core_Token_new(CORE_TOKEN_IDENTIFIER,
                                     lexeme,
                                     strlen(lexeme),
                                     1);
    assertFalse(core_Token_lexemeEquals(token, comparedLexeme));
    core_Token_free(token);
}

static void TokenLexemeEqualsTest3(TestCase *this) {
    const char *lexeme = "foo";
    const char *comparedLexeme = "foobar";
    core_Token *token = core_Token_new(CORE_TOKEN_IDENTIFIER,
                                     lexeme,
                                     strlen(lexeme),
                                     1);
    assertFalse(core_Token_lexemeEquals(token, comparedLexeme));
    core_Token_free(token);
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
