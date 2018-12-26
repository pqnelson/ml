#include <stdlib.h>
#include <stdio.h>
#include <stddef.h>
#include "utils.h"
#include "mml/token.h"
#include "mml/scanner.h"
#include "test.h"
#include "testsuites.h"
// cl /Za /W4 -I .\includes src/scanner_test.c src/scanner.c /link /out:program1.exe
// The "/Za" option forces C89 compliance, which is a double edged sword...

static void TrueIsReservedKeywordTest(TestCase *this) {
    const char *source = "True";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    assertFalse(mml_Scanner_hasNext(scanner));
    assertEqual(MML_TOKEN_TRUE, mml_Token_type(token));
    mml_Scanner_free(scanner);
    mml_Token_free(token);
}

static void FalseIsReservedKeywordTest(TestCase *this) {
    const char *source = "False";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    assertFalse(mml_Scanner_hasNext(scanner));
    assertEqual(MML_TOKEN_FALSE, mml_Token_type(token));
    mml_Scanner_free(scanner);
    mml_Token_free(token);
}

static void IntIsReservedKeywordTest(TestCase *this) {
    const char *source = "Int";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    assertFalse(mml_Scanner_hasNext(scanner));
    assertEqual(MML_TOKEN_INT, mml_Token_type(token));
    mml_Scanner_free(scanner);
    mml_Token_free(token);
}

static void BoolIsReservedKeywordTest(TestCase *this) {
    const char *source = "Bool";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    assertFalse(mml_Scanner_hasNext(scanner));
    assertEqual(MML_TOKEN_BOOL, mml_Token_type(token));
    mml_Scanner_free(scanner);
    mml_Token_free(token);
}

static void FnIsReservedKeywordTest(TestCase *this) {
    const char *source = "fn";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    assertFalse(mml_Scanner_hasNext(scanner));
    assertEqual(MML_TOKEN_FN, mml_Token_type(token));
    mml_Scanner_free(scanner);
    mml_Token_free(token);
}

static void IfIsReservedKeywordTest(TestCase *this) {
    const char *source = "if";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    assertFalse(mml_Scanner_hasNext(scanner));
    assertEqual(MML_TOKEN_IF, mml_Token_type(token));
    mml_Scanner_free(scanner);
    mml_Token_free(token);
}

static void ThenIsReservedKeywordTest(TestCase *this) {
    const char *source = "then";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    assertFalse(mml_Scanner_hasNext(scanner));
    assertEqual(MML_TOKEN_THEN, mml_Token_type(token));
    mml_Scanner_free(scanner);
    mml_Token_free(token);
}

static void ElseIsReservedKeywordTest(TestCase *this) {
    const char *source = "else";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    assertFalse(mml_Scanner_hasNext(scanner));
    assertEqual(MML_TOKEN_ELSE, mml_Token_type(token));
    mml_Scanner_free(scanner);
    mml_Token_free(token);
}

static void LetIsReservedKeywordTest(TestCase *this) {
    const char *source = "let";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    assertFalse(mml_Scanner_hasNext(scanner));
    assertEqual(MML_TOKEN_LET, mml_Token_type(token));
    mml_Scanner_free(scanner);
    mml_Token_free(token);
}

static void LetRecIsReservedKeywordTest(TestCase *this) {
    const char *source = "letrec";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    assertFalse(mml_Scanner_hasNext(scanner));
    assertEqual(MML_TOKEN_LETREC, mml_Token_type(token));
    mml_Scanner_free(scanner);
    mml_Token_free(token);
}

static void InIsReservedKeywordTest(TestCase *this) {
    const char *source = "in";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    assertFalse(mml_Scanner_hasNext(scanner));
    assertEqual(MML_TOKEN_IN, mml_Token_type(token));
    mml_Scanner_free(scanner);
    mml_Token_free(token);
}

static void CaseIsReservedKeywordTest(TestCase *this) {
    const char *source = "case";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    assertFalse(mml_Scanner_hasNext(scanner));
    assertEqual(MML_TOKEN_CASE, mml_Token_type(token));
    mml_Scanner_free(scanner);
    mml_Token_free(token);
}

static void DataIsReservedKeywordTest(TestCase *this) {
    const char *source = "data";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    assertFalse(mml_Scanner_hasNext(scanner));
    assertEqual(MML_TOKEN_DATA, mml_Token_type(token));
    mml_Scanner_free(scanner);
    mml_Token_free(token);
}

static void NewtypeIsReservedKeywordTest(TestCase *this) {
    const char *source = "newtype";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    assertFalse(mml_Scanner_hasNext(scanner));
    assertEqual(MML_TOKEN_NEWTYPE, mml_Token_type(token));
    mml_Scanner_free(scanner);
    mml_Token_free(token);
}

static void ForallIsReservedKeywordTest(TestCase *this) {
    const char *source = "forall";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    assertFalse(mml_Scanner_hasNext(scanner));
    assertEqual(MML_TOKEN_FORALL, mml_Token_type(token));
    mml_Scanner_free(scanner);
    mml_Token_free(token);
}

static void OfIsReservedKeywordTest(TestCase *this) {
    const char *source = "of";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    assertFalse(mml_Scanner_hasNext(scanner));
    assertEqual(MML_TOKEN_OF, mml_Token_type(token));
    mml_Scanner_free(scanner);
    mml_Token_free(token);
}

static void LeftBraceIsPunctuationTest(TestCase *this) {
    const char *source = "{";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    assertFalse(mml_Scanner_hasNext(scanner));
    assertEqual(MML_TOKEN_LEFT_BRACE, mml_Token_type(token));
    mml_Scanner_free(scanner);
    mml_Token_free(token);
}

static void RightBraceIsPunctuationTest(TestCase *this) {
    const char *source = "}";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    assertFalse(mml_Scanner_hasNext(scanner));
    assertEqual(MML_TOKEN_RIGHT_BRACE, mml_Token_type(token));
    mml_Scanner_free(scanner);
    mml_Token_free(token);
}

static void LeftParenIsPunctuationTest(TestCase *this) {
    const char *source = "(";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    assertFalse(mml_Scanner_hasNext(scanner));
    assertEqual(MML_TOKEN_LEFT_PAREN, mml_Token_type(token));
    mml_Scanner_free(scanner);
    mml_Token_free(token);
}

static void RightParenIsPunctuationTest(TestCase *this) {
    const char *source = ")";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    assertFalse(mml_Scanner_hasNext(scanner));
    assertEqual(MML_TOKEN_RIGHT_PAREN, mml_Token_type(token));
    mml_Scanner_free(scanner);
    mml_Token_free(token);
}

static void SemicolonIsPunctuationTest(TestCase *this) {
    const char *source = ";";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    assertFalse(mml_Scanner_hasNext(scanner));
    assertEqual(MML_TOKEN_SEMICOLON, mml_Token_type(token));
    mml_Scanner_free(scanner);
    mml_Token_free(token);
}

static void StarIsPunctuationTest(TestCase *this) {
    const char *source = "*";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    assertFalse(mml_Scanner_hasNext(scanner));
    assertEqual(MML_TOKEN_STAR, mml_Token_type(token));
    mml_Scanner_free(scanner);
    mml_Token_free(token);
}

static void ColonIsPunctuationTest(TestCase *this) {
    const char *source = ":";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    assertFalse(mml_Scanner_hasNext(scanner));
    assertEqual(MML_TOKEN_COLON, mml_Token_type(token));
    mml_Scanner_free(scanner);
    mml_Token_free(token);
}

static void EstiIsPunctuationTest(TestCase *this) {
    const char *source = "::";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    assertFalse(mml_Scanner_hasNext(scanner));
    assertEqual(MML_TOKEN_ESTI, mml_Token_type(token));
    mml_Scanner_free(scanner);
    mml_Token_free(token);
}

static void FnArrowIsPunctuationTest(TestCase *this) {
    const char *source = "->";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    assertFalse(mml_Scanner_hasNext(scanner));
    assertEqual(MML_TOKEN_FN_ARROW, mml_Token_type(token));
    mml_Scanner_free(scanner);
    mml_Token_free(token);
}

static void MinusIsPunctuationTest(TestCase *this) {
    const char *source = "-";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    assertFalse(mml_Scanner_hasNext(scanner));
    assertEqual(MML_TOKEN_MINUS, mml_Token_type(token));
    mml_Scanner_free(scanner);
    mml_Token_free(token);
}

static void EqualsIsPunctuationTest(TestCase *this) {
    const char *source = "=";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    assertFalse(mml_Scanner_hasNext(scanner));
    assertEqual(MML_TOKEN_EQUAL, mml_Token_type(token));
    mml_Scanner_free(scanner);
    mml_Token_free(token);
}

static void PlusIsPunctuationTest(TestCase *this) {
    const char *source = "+";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    assertFalse(mml_Scanner_hasNext(scanner));
    assertEqual(MML_TOKEN_PLUS, mml_Token_type(token));
    mml_Scanner_free(scanner);
    mml_Token_free(token);
}

static void UnderscoreIsPunctuationTest(TestCase *this) {
    const char *source = "_";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    assertFalse(mml_Scanner_hasNext(scanner));
    assertEqual(MML_TOKEN_UNDERSCORE, mml_Token_type(token));
    mml_Scanner_free(scanner);
    mml_Token_free(token);
}

static void ScanAtSignTest(TestCase *this) {
    const char *source = "@";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    assertFalse(mml_Scanner_hasNext(scanner));
    assertEqual(MML_TOKEN_AT_SIGN, mml_Token_type(token));
    mml_Scanner_free(scanner);
    mml_Token_free(token);
}

#define invalidPunctuationTestBody(sym)                      \
    {                                                        \
        const char *source = sym;                            \
        mml_Scanner *scanner = mml_Scanner_new(source);      \
        mml_Token *token = mml_Scanner_next(scanner);        \
        assertFalse(mml_Scanner_hasNext(scanner));           \
        assertEqual(MML_TOKEN_ERROR, mml_Token_type(token)); \
        mml_Scanner_free(scanner);                           \
        mml_Token_free(token);                               \
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
    mml_Token *tokens[7];
    const char *source = "if True\nthen 5\nelse False";
    mml_Scanner *scanner = mml_Scanner_new(source);
    size_t line = 0;
    int i;
    for (i = 0; mml_Scanner_hasNext(scanner) && i < 7; i++) {
        tokens[i] = mml_Scanner_next(scanner);
        if (mml_Token_line(tokens[i]) != line) {
            line = mml_Token_line(tokens[i]);
        }
    }
    tokens[i] = mml_Scanner_next(scanner);
    mml_Scanner_free(scanner);
    assertEqual(i, 6);

    MML_TokenType types[7] = {MML_TOKEN_IF, MML_TOKEN_TRUE,
                              MML_TOKEN_THEN, MML_TOKEN_INTEGER,
                              MML_TOKEN_ELSE, MML_TOKEN_FALSE, MML_TOKEN_EOF};
    size_t lines[7] = {1, 1, 2, 2, 3, 3, 3};
    for(i=0; i < 7; i++) {
        assertEqual(mml_Token_type(tokens[i]), types[i]);
        assertEqual(mml_Token_line(tokens[i]), lines[i]);
        mml_Token_free(tokens[i]);
    }
}

static void LexNestedConditionalTest1(TestCase *this) {
    mml_Token *tokens[14];
    const char *source = "if True\nthen if x = 7 then 5 else x\nelse False";
    mml_Scanner *scanner = mml_Scanner_new(source);
    size_t line = 0;
    int i;
    for (i = 0; mml_Scanner_hasNext(scanner) && i < 13; i++) {
        tokens[i] = mml_Scanner_next(scanner);
        if (mml_Token_line(tokens[i]) != line) {
            line = mml_Token_line(tokens[i]);
        }
    }
    tokens[i] = mml_Scanner_next(scanner);
    mml_Scanner_free(scanner);
    assertEqual(i, 13);
    
    MML_TokenType types[14] = {MML_TOKEN_IF, MML_TOKEN_TRUE,
                               MML_TOKEN_THEN, MML_TOKEN_IF, MML_TOKEN_IDENTIFIER, MML_TOKEN_EQUAL, MML_TOKEN_INTEGER, MML_TOKEN_THEN, MML_TOKEN_INTEGER, MML_TOKEN_ELSE, MML_TOKEN_IDENTIFIER,
                               MML_TOKEN_ELSE, MML_TOKEN_FALSE, MML_TOKEN_EOF};
    size_t lines[14] = {1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3};
    for(i=0; i < 14; i++) {
        assertEqual(mml_Token_type(tokens[i]), types[i]);
        assertEqual(mml_Token_line(tokens[i]), lines[i]);
        mml_Token_free(tokens[i]);
    }
}

static void LexNearReservedKeywordTest1(TestCase *this) {
    const char *source = "iff";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    mml_Scanner_free(scanner);
    assertEqual(mml_Token_type(token), MML_TOKEN_IDENTIFIER);
    mml_Token_free(token);
}

static void SkipWhitespaceTest1(TestCase *this) {
    const char *source = "            iff";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    mml_Scanner_free(scanner);
    assertEqual(mml_Token_type(token), MML_TOKEN_IDENTIFIER);
    mml_Token_free(token);
}

static void SkipWhitespaceTest2(TestCase *this) {
    const char *source = "\t\t\t\tiff";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    mml_Scanner_free(scanner);
    assertEqual(mml_Token_type(token), MML_TOKEN_IDENTIFIER);
    mml_Token_free(token);
}

static void SkipWhitespaceTest3(TestCase *this) {
    const char *source = "\r\f\n\tiff";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    mml_Scanner_free(scanner);
    assertEqual(mml_Token_type(token), MML_TOKEN_IDENTIFIER);
    mml_Token_free(token);
}

static void SkipSimpleCommentTest(TestCase *this) {
    const char *source = "(*this will be thrown away*)iff";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    
    assertFalse(mml_Scanner_hasNext(scanner));
    mml_Scanner_free(scanner);
    
    assertEqual(mml_Token_type(token), MML_TOKEN_IDENTIFIER);
    assertTrue(mml_Token_lexemeEquals(token, "iff"));
    mml_Token_free(token);
}

static void SkipNestedCommentTest(TestCase *this) {
    const char *source = "(*this (*will (*be*) thrown*) away*)iff";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    
    assertFalse(mml_Scanner_hasNext(scanner));
    mml_Scanner_free(scanner);
    
    assertEqual(mml_Token_type(token), MML_TOKEN_IDENTIFIER);
    assertTrue(mml_Token_lexemeEquals(token, "iff"));
    mml_Token_free(token);
}

static void RunawayCommentTest(TestCase *this) {
    const char *source = "(*this (*will (*be*) thrown*) runaway";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    
    assertFalse(mml_Scanner_hasNext(scanner));
    mml_Scanner_free(scanner);
    
    assertEqual(mml_Token_type(token), MML_TOKEN_ERROR);
    assertTrue(mml_Token_lexemeEquals(token, "(*this (*will (*be*) thrown*) runaway"));
    mml_Token_free(token);
}

static void ScanDeclarationTest(TestCase *this) {
    const char *source = "Fork :: Bintree a -> Bintree a -> Bintree a;";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token[11];
    for (int i = 0; i < 11; i++) {
        token[i] = mml_Scanner_next(scanner);
    }
    assertFalse(mml_Scanner_hasNext(scanner));
    mml_Scanner_free(scanner);

    MML_TokenType types[11] = {MML_TOKEN_IDENTIFIER,
                               MML_TOKEN_ESTI,
                               MML_TOKEN_IDENTIFIER, MML_TOKEN_IDENTIFIER,
                               MML_TOKEN_FN_ARROW,
                               MML_TOKEN_IDENTIFIER, MML_TOKEN_IDENTIFIER,
                               MML_TOKEN_FN_ARROW,
                               MML_TOKEN_IDENTIFIER, MML_TOKEN_IDENTIFIER,
                               MML_TOKEN_SEMICOLON};
    for (int i = 0; i < 11; i++) {
        assertEqual(mml_Token_type(token[i]), types[i]);
        mml_Token_free(token[i]);
    }
}

static void ScanPositiveIntegerTest(TestCase *this) {
    const char *source = "13";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    
    assertFalse(mml_Scanner_hasNext(scanner));
    mml_Scanner_free(scanner);
    
    assertEqual(mml_Token_type(token), MML_TOKEN_INTEGER);
    assertTrue(mml_Token_lexemeEquals(token, "13"));
    mml_Token_free(token);
}

static void ScanNegativeIntegerTest(TestCase *this) {
    const char *source = "-13";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    
    assertFalse(mml_Scanner_hasNext(scanner));
    mml_Scanner_free(scanner);
    
    assertEqual(mml_Token_type(token), MML_TOKEN_INTEGER);
    assertTrue(mml_Token_lexemeEquals(token, "-13"));
    mml_Token_free(token);
}

static void InvalidNumberTest(TestCase *this) {
    const char *source = "13a";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    
    assertFalse(mml_Scanner_hasNext(scanner));
    mml_Scanner_free(scanner);
    
    assertEqual(mml_Token_type(token), MML_TOKEN_ERROR);
    assertTrue(mml_Token_lexemeEquals(token, "13a"));
    mml_Token_free(token);
}

static void AddingTwoNumbersTest(TestCase *this) {
    const char *source = "13+2";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    
    assertTrue(mml_Scanner_hasNext(scanner));
    assertEqual(mml_Token_type(token), MML_TOKEN_INTEGER);
    assertTrue(mml_Token_lexemeEquals(token, "13"));

    mml_Token_free(token);
    token = mml_Scanner_next(scanner);
    
    assertTrue(mml_Scanner_hasNext(scanner));
    assertEqual(mml_Token_type(token), MML_TOKEN_PLUS);
    assertTrue(mml_Token_lexemeEquals(token, "+"));
    
    mml_Token_free(token);
    token = mml_Scanner_next(scanner);
    
    assertFalse(mml_Scanner_hasNext(scanner));
    assertEqual(mml_Token_type(token), MML_TOKEN_INTEGER);
    assertTrue(mml_Token_lexemeEquals(token, "2"));
    
    mml_Scanner_free(scanner);
    mml_Token_free(token);
}

static void ScanStringTest1(TestCase *this) {
    const char *source = "\"13+2\"";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    
    assertFalse(mml_Scanner_hasNext(scanner));
    assertEqual(mml_Token_type(token), MML_TOKEN_STRING);
    assertTrue(mml_Token_lexemeEquals(token, "\"13+2\""));
    
    mml_Scanner_free(scanner);
    mml_Token_free(token);
}

static void ScanNestedStringTest(TestCase *this) {
    const char *source = "\"13+\\\"2\"";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    
    assertFalse(mml_Scanner_hasNext(scanner));
    assertEqual(mml_Token_type(token), MML_TOKEN_STRING);
    assertTrue(mml_Token_lexemeEquals(token, "\"13+\\\"2\""));
    
    mml_Scanner_free(scanner);
    mml_Token_free(token);
}

static void ScanRunawayStringTest(TestCase *this) {
    // runaway string test
    const char *source = "\"13+\\\"2";
    mml_Scanner *scanner = mml_Scanner_new(source);
    mml_Token *token = mml_Scanner_next(scanner);
    
    assertFalse(mml_Scanner_hasNext(scanner));
    assertEqual(mml_Token_type(token), MML_TOKEN_ERROR);
    assertTrue(mml_Token_lexemeEquals(token, "\"13+\\\"2"));
    
    mml_Scanner_free(scanner);
    mml_Token_free(token);
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
