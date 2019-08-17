#include <stdlib.h>
#include <stdio.h>
#include <stddef.h>
#include "utils.h"
#include "core/token.h"
#include "core/scanner.h"
#include "test.h"
#include "testsuites.h"
// cl /Za /W4 -I .\includes src/scanner_test.c src/scanner.c /link /out:program1.exe
// The "/Za" option forces C89 compliance, which is a double edged sword...

static void TrueIsReservedKeywordTest(TestCase *this) {
    const char *source = "True";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    assertFalse(core_Scanner_hasNext(scanner));
    assertEqual(CORE_TOKEN_TRUE, core_Token_type(token));
    core_Scanner_free(scanner);
    core_Token_free(token);
}

static void FalseIsReservedKeywordTest(TestCase *this) {
    const char *source = "False";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    assertFalse(core_Scanner_hasNext(scanner));
    assertEqual(CORE_TOKEN_FALSE, core_Token_type(token));
    core_Scanner_free(scanner);
    core_Token_free(token);
}

static void IntIsReservedKeywordTest(TestCase *this) {
    const char *source = "Int";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    assertFalse(core_Scanner_hasNext(scanner));
    assertEqual(CORE_TOKEN_INT, core_Token_type(token));
    core_Scanner_free(scanner);
    core_Token_free(token);
}

static void BoolIsReservedKeywordTest(TestCase *this) {
    const char *source = "Bool";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    assertFalse(core_Scanner_hasNext(scanner));
    assertEqual(CORE_TOKEN_BOOL, core_Token_type(token));
    core_Scanner_free(scanner);
    core_Token_free(token);
}

static void FnIsReservedKeywordTest(TestCase *this) {
    const char *source = "fn";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    assertFalse(core_Scanner_hasNext(scanner));
    assertEqual(CORE_TOKEN_FN, core_Token_type(token));
    core_Scanner_free(scanner);
    core_Token_free(token);
}

static void IfIsReservedKeywordTest(TestCase *this) {
    const char *source = "if";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    assertFalse(core_Scanner_hasNext(scanner));
    assertEqual(CORE_TOKEN_IF, core_Token_type(token));
    core_Scanner_free(scanner);
    core_Token_free(token);
}

static void ThenIsReservedKeywordTest(TestCase *this) {
    const char *source = "then";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    assertFalse(core_Scanner_hasNext(scanner));
    assertEqual(CORE_TOKEN_THEN, core_Token_type(token));
    core_Scanner_free(scanner);
    core_Token_free(token);
}

static void ElseIsReservedKeywordTest(TestCase *this) {
    const char *source = "else";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    assertFalse(core_Scanner_hasNext(scanner));
    assertEqual(CORE_TOKEN_ELSE, core_Token_type(token));
    core_Scanner_free(scanner);
    core_Token_free(token);
}

static void LetIsReservedKeywordTest(TestCase *this) {
    const char *source = "let";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    assertFalse(core_Scanner_hasNext(scanner));
    assertEqual(CORE_TOKEN_LET, core_Token_type(token));
    core_Scanner_free(scanner);
    core_Token_free(token);
}

static void LetRecIsReservedKeywordTest(TestCase *this) {
    const char *source = "letrec";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    assertFalse(core_Scanner_hasNext(scanner));
    assertEqual(CORE_TOKEN_LETREC, core_Token_type(token));
    core_Scanner_free(scanner);
    core_Token_free(token);
}

static void InIsReservedKeywordTest(TestCase *this) {
    const char *source = "in";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    assertFalse(core_Scanner_hasNext(scanner));
    assertEqual(CORE_TOKEN_IN, core_Token_type(token));
    core_Scanner_free(scanner);
    core_Token_free(token);
}

static void CaseIsReservedKeywordTest(TestCase *this) {
    const char *source = "case";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    assertFalse(core_Scanner_hasNext(scanner));
    assertEqual(CORE_TOKEN_CASE, core_Token_type(token));
    core_Scanner_free(scanner);
    core_Token_free(token);
}

static void DataIsReservedKeywordTest(TestCase *this) {
    const char *source = "data";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    assertFalse(core_Scanner_hasNext(scanner));
    assertEqual(CORE_TOKEN_DATA, core_Token_type(token));
    core_Scanner_free(scanner);
    core_Token_free(token);
}

static void NewtypeIsReservedKeywordTest(TestCase *this) {
    const char *source = "newtype";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    assertFalse(core_Scanner_hasNext(scanner));
    assertEqual(CORE_TOKEN_NEWTYPE, core_Token_type(token));
    core_Scanner_free(scanner);
    core_Token_free(token);
}

static void ForallIsReservedKeywordTest(TestCase *this) {
    const char *source = "forall";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    assertFalse(core_Scanner_hasNext(scanner));
    assertEqual(CORE_TOKEN_FORALL, core_Token_type(token));
    core_Scanner_free(scanner);
    core_Token_free(token);
}

static void OfIsReservedKeywordTest(TestCase *this) {
    const char *source = "of";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    assertFalse(core_Scanner_hasNext(scanner));
    assertEqual(CORE_TOKEN_OF, core_Token_type(token));
    core_Scanner_free(scanner);
    core_Token_free(token);
}

static void LeftBraceIsPunctuationTest(TestCase *this) {
    const char *source = "{";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    assertFalse(core_Scanner_hasNext(scanner));
    assertEqual(CORE_TOKEN_LEFT_BRACE, core_Token_type(token));
    core_Scanner_free(scanner);
    core_Token_free(token);
}

static void RightBraceIsPunctuationTest(TestCase *this) {
    const char *source = "}";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    assertFalse(core_Scanner_hasNext(scanner));
    assertEqual(CORE_TOKEN_RIGHT_BRACE, core_Token_type(token));
    core_Scanner_free(scanner);
    core_Token_free(token);
}

static void LeftParenIsPunctuationTest(TestCase *this) {
    const char *source = "(";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    assertFalse(core_Scanner_hasNext(scanner));
    assertEqual(CORE_TOKEN_LEFT_PAREN, core_Token_type(token));
    core_Scanner_free(scanner);
    core_Token_free(token);
}

static void RightParenIsPunctuationTest(TestCase *this) {
    const char *source = ")";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    assertFalse(core_Scanner_hasNext(scanner));
    assertEqual(CORE_TOKEN_RIGHT_PAREN, core_Token_type(token));
    core_Scanner_free(scanner);
    core_Token_free(token);
}

static void SemicolonIsPunctuationTest(TestCase *this) {
    const char *source = ";";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    assertFalse(core_Scanner_hasNext(scanner));
    assertEqual(CORE_TOKEN_SEMICOLON, core_Token_type(token));
    core_Scanner_free(scanner);
    core_Token_free(token);
}

static void StarIsPunctuationTest(TestCase *this) {
    const char *source = "*";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    assertFalse(core_Scanner_hasNext(scanner));
    assertEqual(CORE_TOKEN_STAR, core_Token_type(token));
    core_Scanner_free(scanner);
    core_Token_free(token);
}

static void ColonIsPunctuationTest(TestCase *this) {
    const char *source = ":";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    assertFalse(core_Scanner_hasNext(scanner));
    assertEqual(CORE_TOKEN_COLON, core_Token_type(token));
    core_Scanner_free(scanner);
    core_Token_free(token);
}

static void EstiIsPunctuationTest(TestCase *this) {
    const char *source = "::";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    assertFalse(core_Scanner_hasNext(scanner));
    assertEqual(CORE_TOKEN_ESTI, core_Token_type(token));
    core_Scanner_free(scanner);
    core_Token_free(token);
}

static void FnArrowIsPunctuationTest(TestCase *this) {
    const char *source = "->";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    assertFalse(core_Scanner_hasNext(scanner));
    assertEqual(CORE_TOKEN_FN_ARROW, core_Token_type(token));
    core_Scanner_free(scanner);
    core_Token_free(token);
}

static void MinusIsPunctuationTest(TestCase *this) {
    const char *source = "-";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    assertFalse(core_Scanner_hasNext(scanner));
    assertEqual(CORE_TOKEN_MINUS, core_Token_type(token));
    core_Scanner_free(scanner);
    core_Token_free(token);
}

static void EqualsIsPunctuationTest(TestCase *this) {
    const char *source = "=";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    assertFalse(core_Scanner_hasNext(scanner));
    assertEqual(CORE_TOKEN_EQUAL, core_Token_type(token));
    core_Scanner_free(scanner);
    core_Token_free(token);
}

static void PlusIsPunctuationTest(TestCase *this) {
    const char *source = "+";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    assertFalse(core_Scanner_hasNext(scanner));
    assertEqual(CORE_TOKEN_PLUS, core_Token_type(token));
    core_Scanner_free(scanner);
    core_Token_free(token);
}

static void UnderscoreIsPunctuationTest(TestCase *this) {
    const char *source = "_";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    assertFalse(core_Scanner_hasNext(scanner));
    assertEqual(CORE_TOKEN_UNDERSCORE, core_Token_type(token));
    core_Scanner_free(scanner);
    core_Token_free(token);
}

static void ScanAtSignTest(TestCase *this) {
    const char *source = "@";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    assertFalse(core_Scanner_hasNext(scanner));
    assertEqual(CORE_TOKEN_AT_SIGN, core_Token_type(token));
    core_Scanner_free(scanner);
    core_Token_free(token);
}

#define invalidPunctuationTestBody(sym)                      \
    {                                                        \
        const char *source = sym;                            \
        core_Scanner *scanner = core_Scanner_new(source);      \
        core_Token *token = core_Scanner_next(scanner);        \
        assertFalse(core_Scanner_hasNext(scanner));           \
        assertEqual(CORE_TOKEN_ERROR, core_Token_type(token)); \
        core_Scanner_free(scanner);                           \
        core_Token_free(token);                               \
   }

static void ScanQuestionMarkTest(TestCase *this) {
    invalidPunctuationTestBody("?");
}

static void ScanGTTest(TestCase *this) {
    invalidPunctuationTestBody(">");
}
static void ScanLTTest(TestCase *this) {
    invalidPunctuationTestBody("<");
}

static void ScanApostropheTest(TestCase *this) {
    invalidPunctuationTestBody("'");
}

static void ScanLeftBracketTest(TestCase *this) {
    invalidPunctuationTestBody("[");
}

static void ScanRightBracketTest(TestCase *this) {
    invalidPunctuationTestBody("]");
}

static void ScanExclamationPointTest(TestCase *this) {
    invalidPunctuationTestBody("!");
}

static void ScanHashTagTest(TestCase *this) {
    invalidPunctuationTestBody("#");
}

static void ScanDollarSignTest(TestCase *this) {
    invalidPunctuationTestBody("$");
}

static void ScanPercentSignTest(TestCase *this) {
    invalidPunctuationTestBody("%");
}

static void ScanCaretTest(TestCase *this) {
    invalidPunctuationTestBody("^");
}

static void ScanAmpersandTest(TestCase *this) {
    invalidPunctuationTestBody("&");
}

static void ScanGraveAccentTest(TestCase *this) {
    invalidPunctuationTestBody("`");
}

static void ScanTildeTest(TestCase *this) {
    invalidPunctuationTestBody("~");
}

#undef invalidPunctuationTestBody

static void LexBasicConditionalTest(TestCase *this) {
    core_Token *tokens[7];
    const char *source = "if True\nthen 5\nelse False";
    core_Scanner *scanner = core_Scanner_new(source);
    size_t line = 0;
    int i;
    for (i = 0; core_Scanner_hasNext(scanner) && i < 7; i++) {
        tokens[i] = core_Scanner_next(scanner);
        if (core_Token_line(tokens[i]) != line) {
            line = core_Token_line(tokens[i]);
        }
    }
    tokens[i] = core_Scanner_next(scanner);
    core_Scanner_free(scanner);
    assertEqual(i, 6);

    CORE_TokenType types[7] = {CORE_TOKEN_IF, CORE_TOKEN_TRUE,
                              CORE_TOKEN_THEN, CORE_TOKEN_INTEGER,
                              CORE_TOKEN_ELSE, CORE_TOKEN_FALSE, CORE_TOKEN_EOF};
    size_t lines[7] = {1, 1, 2, 2, 3, 3, 3};
    for(i=0; i < 7; i++) {
        assertEqual(core_Token_type(tokens[i]), types[i]);
        assertEqual(core_Token_line(tokens[i]), lines[i]);
        core_Token_free(tokens[i]);
    }
}

static void LexNestedConditionalTest1(TestCase *this) {
    core_Token *tokens[14];
    const char *source = "if True\nthen if x = 7 then 5 else x\nelse False";
    core_Scanner *scanner = core_Scanner_new(source);
    size_t line = 0;
    int i;
    for (i = 0; core_Scanner_hasNext(scanner) && i < 13; i++) {
        tokens[i] = core_Scanner_next(scanner);
        if (core_Token_line(tokens[i]) != line) {
            line = core_Token_line(tokens[i]);
        }
    }
    tokens[i] = core_Scanner_next(scanner);
    core_Scanner_free(scanner);
    assertEqual(i, 13);
    
    CORE_TokenType types[14] = {CORE_TOKEN_IF, CORE_TOKEN_TRUE,
                               CORE_TOKEN_THEN, CORE_TOKEN_IF, CORE_TOKEN_IDENTIFIER, CORE_TOKEN_EQUAL, CORE_TOKEN_INTEGER, CORE_TOKEN_THEN, CORE_TOKEN_INTEGER, CORE_TOKEN_ELSE, CORE_TOKEN_IDENTIFIER,
                               CORE_TOKEN_ELSE, CORE_TOKEN_FALSE, CORE_TOKEN_EOF};
    size_t lines[14] = {1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3};
    for(i=0; i < 14; i++) {
        assertEqual(core_Token_type(tokens[i]), types[i]);
        assertEqual(core_Token_line(tokens[i]), lines[i]);
        core_Token_free(tokens[i]);
    }
}

static void LexNearReservedKeywordTest1(TestCase *this) {
    const char *source = "iff";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    core_Scanner_free(scanner);
    assertEqual(core_Token_type(token), CORE_TOKEN_IDENTIFIER);
    core_Token_free(token);
}

static void SkipWhitespaceTest1(TestCase *this) {
    const char *source = "            iff";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    core_Scanner_free(scanner);
    assertEqual(core_Token_type(token), CORE_TOKEN_IDENTIFIER);
    core_Token_free(token);
}

static void SkipWhitespaceTest2(TestCase *this) {
    const char *source = "\t\t\t\tiff";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    core_Scanner_free(scanner);
    assertEqual(core_Token_type(token), CORE_TOKEN_IDENTIFIER);
    core_Token_free(token);
}

static void SkipWhitespaceTest3(TestCase *this) {
    const char *source = "\r\f\n\tiff";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    core_Scanner_free(scanner);
    assertEqual(core_Token_type(token), CORE_TOKEN_IDENTIFIER);
    core_Token_free(token);
}

static void SkipSimpleCommentTest(TestCase *this) {
    const char *source = "(*this will be thrown away*)iff";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    
    assertFalse(core_Scanner_hasNext(scanner));
    core_Scanner_free(scanner);
    
    assertEqual(core_Token_type(token), CORE_TOKEN_IDENTIFIER);
    assertTrue(core_Token_lexemeEquals(token, "iff"));
    core_Token_free(token);
}

static void SkipNestedCommentTest(TestCase *this) {
    const char *source = "(*this (*will (*be*) thrown*) away*)iff";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    
    assertFalse(core_Scanner_hasNext(scanner));
    core_Scanner_free(scanner);
    
    assertEqual(core_Token_type(token), CORE_TOKEN_IDENTIFIER);
    assertTrue(core_Token_lexemeEquals(token, "iff"));
    core_Token_free(token);
}

static void RunawayCommentTest(TestCase *this) {
    const char *source = "(*this (*will (*be*) thrown*) runaway";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    
    assertFalse(core_Scanner_hasNext(scanner));
    core_Scanner_free(scanner);
    
    assertEqual(core_Token_type(token), CORE_TOKEN_ERROR);
    assertTrue(core_Token_lexemeEquals(token, "(*this (*will (*be*) thrown*) runaway"));
    core_Token_free(token);
}

static void ScanDeclarationTest(TestCase *this) {
    const char *source = "Fork :: Bintree a -> Bintree a -> Bintree a;";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token[11];
    for (int i = 0; i < 11; i++) {
        token[i] = core_Scanner_next(scanner);
    }
    assertFalse(core_Scanner_hasNext(scanner));
    core_Scanner_free(scanner);

    CORE_TokenType types[11] = {CORE_TOKEN_IDENTIFIER,
                               CORE_TOKEN_ESTI,
                               CORE_TOKEN_IDENTIFIER, CORE_TOKEN_IDENTIFIER,
                               CORE_TOKEN_FN_ARROW,
                               CORE_TOKEN_IDENTIFIER, CORE_TOKEN_IDENTIFIER,
                               CORE_TOKEN_FN_ARROW,
                               CORE_TOKEN_IDENTIFIER, CORE_TOKEN_IDENTIFIER,
                               CORE_TOKEN_SEMICOLON};
    for (int i = 0; i < 11; i++) {
        assertEqual(core_Token_type(token[i]), types[i]);
        core_Token_free(token[i]);
    }
}

static void ScanPositiveIntegerTest(TestCase *this) {
    const char *source = "13";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    
    assertFalse(core_Scanner_hasNext(scanner));
    core_Scanner_free(scanner);
    
    assertEqual(core_Token_type(token), CORE_TOKEN_INTEGER);
    assertTrue(core_Token_lexemeEquals(token, "13"));
    core_Token_free(token);
}

static void ScanNegativeIntegerTest(TestCase *this) {
    const char *source = "-13";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    
    assertFalse(core_Scanner_hasNext(scanner));
    core_Scanner_free(scanner);
    
    assertEqual(core_Token_type(token), CORE_TOKEN_INTEGER);
    assertTrue(core_Token_lexemeEquals(token, "-13"));
    core_Token_free(token);
}

static void InvalidNumberTest(TestCase *this) {
    const char *source = "13a";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    
    assertFalse(core_Scanner_hasNext(scanner));
    core_Scanner_free(scanner);
    
    assertEqual(core_Token_type(token), CORE_TOKEN_ERROR);
    assertTrue(core_Token_lexemeEquals(token, "13a"));
    core_Token_free(token);
}

static void AddingTwoNumbersTest(TestCase *this) {
    const char *source = "13+2";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    
    assertTrue(core_Scanner_hasNext(scanner));
    assertEqual(core_Token_type(token), CORE_TOKEN_INTEGER);
    assertTrue(core_Token_lexemeEquals(token, "13"));

    core_Token_free(token);
    token = core_Scanner_next(scanner);
    
    assertTrue(core_Scanner_hasNext(scanner));
    assertEqual(core_Token_type(token), CORE_TOKEN_PLUS);
    assertTrue(core_Token_lexemeEquals(token, "+"));
    
    core_Token_free(token);
    token = core_Scanner_next(scanner);
    
    assertFalse(core_Scanner_hasNext(scanner));
    assertEqual(core_Token_type(token), CORE_TOKEN_INTEGER);
    assertTrue(core_Token_lexemeEquals(token, "2"));
    
    core_Scanner_free(scanner);
    core_Token_free(token);
}

static void ScanStringTest1(TestCase *this) {
    const char *source = "\"13+2\"";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    
    assertFalse(core_Scanner_hasNext(scanner));
    assertEqual(core_Token_type(token), CORE_TOKEN_STRING);
    assertTrue(core_Token_lexemeEquals(token, "\"13+2\""));
    
    core_Scanner_free(scanner);
    core_Token_free(token);
}

static void ScanNestedStringTest(TestCase *this) {
    const char *source = "\"13+\\\"2\"";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    
    assertFalse(core_Scanner_hasNext(scanner));
    assertEqual(core_Token_type(token), CORE_TOKEN_STRING);
    assertTrue(core_Token_lexemeEquals(token, "\"13+\\\"2\""));
    
    core_Scanner_free(scanner);
    core_Token_free(token);
}

static void ScanRunawayStringTest(TestCase *this) {
    // runaway string test
    const char *source = "\"13+\\\"2";
    core_Scanner *scanner = core_Scanner_new(source);
    core_Token *token = core_Scanner_next(scanner);
    
    assertFalse(core_Scanner_hasNext(scanner));
    assertEqual(core_Token_type(token), CORE_TOKEN_ERROR);
    assertTrue(core_Token_lexemeEquals(token, "\"13+\\\"2"));
    
    core_Scanner_free(scanner);
    core_Token_free(token);
}


#ifdef add_test
#undef add_test
#endif
#define add_test(name) TestSuite_addTest(currentSuite, test(name))

void initScannerSuite() {
    TestSuite* currentSuite;
    suite(currentSuite);

    add_test(TrueIsReservedKeywordTest);
    add_test(FalseIsReservedKeywordTest);
    add_test(IntIsReservedKeywordTest);
    add_test(BoolIsReservedKeywordTest);
    add_test(FnIsReservedKeywordTest);
    add_test(IfIsReservedKeywordTest);
    add_test(ThenIsReservedKeywordTest);
    add_test(ElseIsReservedKeywordTest);
    add_test(LetIsReservedKeywordTest);
    add_test(LetRecIsReservedKeywordTest);
    add_test(InIsReservedKeywordTest);
    add_test(CaseIsReservedKeywordTest);
    add_test(DataIsReservedKeywordTest);
    add_test(NewtypeIsReservedKeywordTest);
    add_test(ForallIsReservedKeywordTest);
    add_test(OfIsReservedKeywordTest);
    add_test(LeftBraceIsPunctuationTest);
    add_test(RightBraceIsPunctuationTest);
    add_test(LeftParenIsPunctuationTest);
    add_test(RightParenIsPunctuationTest);
    add_test(SemicolonIsPunctuationTest);
    add_test(StarIsPunctuationTest);
    add_test(ColonIsPunctuationTest);
    add_test(EstiIsPunctuationTest);
    add_test(FnArrowIsPunctuationTest);
    add_test(MinusIsPunctuationTest);
    add_test(EqualsIsPunctuationTest);
    add_test(PlusIsPunctuationTest);
    add_test(UnderscoreIsPunctuationTest);
    add_test(ScanQuestionMarkTest);
    add_test(ScanGTTest);
    add_test(ScanLTTest);
    add_test(ScanApostropheTest);
    add_test(ScanLeftBracketTest);
    add_test(ScanRightBracketTest);
    add_test(ScanExclamationPointTest);
    add_test(ScanAtSignTest);
    add_test(ScanHashTagTest);
    add_test(ScanDollarSignTest);
    add_test(ScanPercentSignTest);
    add_test(ScanCaretTest);
    add_test(ScanAmpersandTest);
    add_test(ScanGraveAccentTest);
    add_test(ScanTildeTest);
    add_test(LexBasicConditionalTest);
    add_test(LexNestedConditionalTest1);
    add_test(LexNearReservedKeywordTest1);
    add_test(SkipWhitespaceTest1);
    add_test(SkipWhitespaceTest2);
    add_test(SkipWhitespaceTest3);
    add_test(SkipSimpleCommentTest);
    add_test(SkipNestedCommentTest);
    add_test(RunawayCommentTest);
    add_test(ScanDeclarationTest);
    add_test(ScanPositiveIntegerTest);
    add_test(ScanNegativeIntegerTest);
    add_test(InvalidNumberTest);
    add_test(AddingTwoNumbersTest);
    add_test(ScanStringTest1);
    add_test(ScanNestedStringTest);
    add_test(ScanRunawayStringTest);
}
#undef add_test
