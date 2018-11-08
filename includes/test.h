/**
 * Basic xUnit testing facilities.
 * 
 * Use these functions to create test cases, test suites, and have them
 * added to the ambient global test runner variable.
 *
 * A new test case should look like:
 * <pre>
 * void randomTestCase(struct TestCase *this) {
 *    // setup
 *    assertEqual(lhs, rhs);
 *    // teardown
 * }
 * </pre>
 * The parameter must be <code>TestCase* this</code> for macros to work.
 * 
 * At the bottom of the test file, you should have a {@code initClassSuite()}
 * function which has a <code>TestSuite* currentSuite</code> followed
 * by a call {@code suite(currentSuite)} macro first, then each line should
 * be add to the <code>currentSuite</code> test suite the test case
 * created via a {@code test(randomTestCase)} declaration.
 * 
 * @author Alex Nelson <pqnelson@gmail.com>
 * @date July 28, 2018
 * @see http://xunitpatterns.com/Testcase%20Object.html
 */
#ifndef TEST_H
#define TEST_H

#include <sys/time.h>

/* ** test case ***/
typedef enum {
    TEST_RESULT_UNTESTED = 0,
    TEST_RESULT_SUCCESS  = 1,
    TEST_RESULT_SKIPPED  = 2,
    TEST_RESULT_FAILURE  = 3,
    TEST_RESULT_ERROR    = 4
} TestResult;

typedef struct TestCase {
    void (*run)(struct TestCase *this);
    const char *name;
    const char *classname;
    TestResult result;
    char *message;
    struct timeval start;
    struct timeval stop;
    double interval;
    struct TestCase *next;
} TestCase;

TestCase* TestCase_new(void (*run)(struct TestCase *this),
                       char *_name,
                       char *_classname);
void TestCase_free(TestCase *test);
void TestCase_run(TestCase *test);
void TestCase_printToScreen(TestCase *test);
void TestCase_printXML(TestCase *test, FILE *xml);

/**
 * Adds a test case to the current suite.
 *
 * Given a <code>void fn(TestCase *this)</code> function identifier, create
 * a new \ref TestCase object for it. Initializes the class name to
 * the name of the current file.
 * 
 * @param name The name of a function containing unit tests
 */
#define test(name) TestCase_new(name, #name, __FILE__)

/* This is a lot of macro black magic to get <code>assertEqual()</code>
 * working properly with variadic arguments.
 */
#define TestCase_isRunnable(test) (test->result == TEST_RESULT_SUCCESS \
                                   || test->result == TEST_RESULT_UNTESTED)

#define TestCase_markSuccess() (this->result = TEST_RESULT_SUCCESS)

#define TestCase_markFail(msg) { this->result = TEST_RESULT_FAILURE; \
    this->message = msg;                                             \
    }

#define assertEqualHelper(lhs, rhs, compare, msg, ...)   \
    if (TestCase_isRunnable(this)) {                     \
        if (compare((lhs), (rhs))) {                     \
             TestCase_markSuccess();                     \
        } else {                                         \
            TestCase_markFail(msg);                      \
            printf("%s FAIL: %s\n", this->name, msg);    \
        }                                                \
    } else { }
#define xstr(x) #x
#define str(x) xstr(x)
// The empty variadic arguments consumes a third argument, which isn't
// needed anyways, hence the underscore argument.
#define _assertEqual2(lhs, rhs, _)                                         \
    if (TestCase_isRunnable(this)) {                                       \
        if ((lhs) == (rhs)) {                                              \
             TestCase_markSuccess();                                       \
        } else {                                                           \
            TestCase_markFail(str(lhs) " != " str(rhs));                   \
            printf("%s FAIL: %s\n", this->name, str(lhs) " != " str(rhs)); \
        }                                                                  \
    } else { }
#define _assertEqual3(lhs, rhs, compare) \
    assertEqualHelper(lhs, rhs, compare, "!" str(compare) "(" str(lhs) ", " str(rhs) ")")
#define _assertEqual4(lhs, rhs, compare, msg) \
    assertEqualHelper(lhs, rhs, compare, msg)

#define _GET_NTH_ARG(_3, _2, _1, N, ...) N
#define COUNT_VARARGS(...) _GET_NTH_ARG(__VAR_ARGS__, 4, 3, 2)
#define _concat(x, y) x ## y
#define concat(x, y) _concat(x, y)
/**
 * Asserts two results are equal.
 * 
 * If two results are equal, mark the test as a success. Otherwise, mark
 * the test as a failure.
 * 
 * @param lhs The value on the left-hand side of the equality test.
 * @param rhs The value on the right-hand side of the equality test.
 * @param compare The equality function, defaults to the naive
 *        <code>(lhs) == (rhs)</code>.
 * @param msg User-provided message shown upon failure, defaults to
 *        <code>testCase->name " FAIL: " str(lhs) != str(rhs)</code>.
 */
#define assertEqual(lhs, rhs, ...) concat(_assertEqual, COUNT_VARARGS(__VA_ARGS__)) (lhs, rhs, __VA_ARGS__)

/**
 * @struct TestSuite test.h
 *
 * A composite of \ref TestCase objects. Keeps track of useful metadata
 * like success, failure count, etc.
 *
 * @var interval The 'interval' is the time to run the test suite in milleseconds (no smaller than the sum of the intervals of the test cases).
 * @invariant failures + skipped + errors <= tests
 * @invariant tests >= 0
 * @invariant interval >= 0.0
 */
typedef struct TestSuite {
    TestCase *first;
    TestCase *last;
    char *name;
    int failures;
    int tests;
    int skipped;
    int errors;
    struct timeval start;
    struct timeval stop;
    double interval;
    struct TestSuite *next;
} TestSuite;

/**
 * @def suite()
 * Allocates memory for the <code>currentSuite</code> static variable, and
 * adds it to the ambient \ref g_runner test runner.
 *
 * @b Important:
 * Must be the first thing called in the test init function before calling
 * <code>test(testCaseName)</code>.
 */
#define suite(currentSuite) { (currentSuite) = TestSuite_new(__FILE__);  \
        TestRunner_add(g_runner, (currentSuite)); }

TestSuite* TestSuite_new(char *name);
void TestSuite_free(TestSuite *suite);
void TestSuite_run(TestSuite *suite);
void TestSuite_addTest(TestSuite *suite, TestCase *test);
void TestSuite_printXML(TestSuite *suite, FILE *xml);
void TestSuite_printToScreen(TestSuite *suite);

/**
 * @struct TestRunner test.h
 *
 * The composite pattern for a collection of \ref TestSuite objects.
 * The user shouldn't ever interact with this code, really.
 */
typedef struct TestRunner {
    TestSuite *first;
    TestSuite *last;
} TestRunner;
/**
 * The global test runner which will run the test suites.
 *
 * You should never really need to interact with this quantity.
 */
extern struct TestRunner *g_runner;

TestRunner* TestRunner_new();
void TestRunner_free(TestRunner *runner);
void TestRunner_add(TestRunner *runner, TestSuite *suite);
void TestRunner_run(TestRunner *runner);
void TestRunner_printToScreen(TestRunner *runner);
void TestRunner_printXML(TestRunner *runner, FILE *xml);

#endif /* TEST_H */
