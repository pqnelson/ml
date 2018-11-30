/**
 * @file includes/test.h
 * 
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
 * The parameter must be <code>TestCase *this</code> for macros to work.
 * 
 * At the bottom of the test file, you should have a
 * <code>initClassSuite()</code> function which has a
 * <code>TestSuite *currentSuite</code> followed by a call
 * <code>suite(currentSuite)</code> macro first, then each line should
 * be add to the <code>currentSuite</code> test suite the test case
 * created via a <code>test(randomTestCase)</code> declaration. For example:
 * <pre>
 * void initFooSuite() {
 *     TestSuite *currentSuite;
 *     suite(currentSuite);
 *     TestSuite_addTest(currentSuite, test(randomTestCase));
 *     // and so on
 * }
 * </pre>
 *
 * @TODO Add an @c assertTrue macro, and ostensibly an @c assertFalse one.
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

/**
 * Wrapper around a single unit test.
 *
 * Really this is an adapter pattern or a decarator (since the TestCase
 * tracks useful metadata).
 * 
 * <b>Important:</b> unit tests must have signature
 * <code>void unitTest(struct TestCase *this);</code> for this entire
 * framework to function.
 *
 * @invariant <code>stop</code> is never earlier than <code>start</code>,
 * when both are defined.
 * @invariant When @c start and @c stop are both defined, we have <code>interval = stop - start</code> in milliseconds.
 * @invariant <code>next</code> is either <code>NULL</code> or never changed
 * once assigned.
 */
typedef struct TestCase {
    void (*run)(struct TestCase *this);
    const char *name; /**< The name of the function describing the unit test. */
    const char *classname; /**< Since each object gets its own module, this is equivalent to the filename. JUnit XML compliance compels us to call it the "class" name, however. */
    TestResult result; /**< Stores the success/fail flag for the unit test. */
    char *message;
    struct timeval start;
    struct timeval stop;
    double interval; /**< Simply <code>stop - start</code> in milliseconds. */
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


/** @cond DEV */
/* This is a lot of macro black magic to get <code>assertEqual()</code>
 * working properly with variadic arguments.
 */
#define TestCase_isRunnable(test) (test->result == TEST_RESULT_SUCCESS \
                                   || test->result == TEST_RESULT_UNTESTED)

#define TestCase_markSuccess() (this->result = TEST_RESULT_SUCCESS)

#define TestCase_markFail(msg) { this->result = TEST_RESULT_FAILURE; \
        this->message = (msg);                                       \
    }

#define assertEqualHelper(lhs, rhs, compare, msg, ...)   \
    if (TestCase_isRunnable(this)) {                     \
        if (compare((lhs), (rhs))) {                     \
             TestCase_markSuccess();                     \
        } else {                                         \
            TestCase_markFail(msg);                      \
            printf("%s FAIL: %s\n", this->name, (msg));  \
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

#define assertTrue(cond)                                                  \
    if (TestCase_isRunnable(this)) {                                      \
        if (cond) {                                                       \
             TestCase_markSuccess();                                      \
        } else {                                                          \
            TestCase_markFail(str(cond) " is FALSE ");                    \
            printf("%s FAIL: %s\n", this->name, str(cond) " is FALSE");   \
        }                                                                 \
    } else { }
#define assertFalse(cond)                                                 \
    if (TestCase_isRunnable(this)) {                                      \
        if (!cond) {                                                      \
             TestCase_markSuccess();                                      \
        } else {                                                          \
            TestCase_markFail(str(cond) " is TRUE, expected FALSE ");     \
            printf("%s FAIL: %s\n", this->name, str(cond) " is TRUE, expected FALSE");   \
        }                                                                 \
    } else { }

#define _GET_NTH_ARG(_3, _2, _1, N, ...) N
#define COUNT_VARARGS(...) _GET_NTH_ARG(__VAR_ARGS__, 4, 3, 2)
#define _concat(x, y) x ## y
#define concat(x, y) _concat(x, y)
/** @endcond */

/**
 * Asserts two results are equal.
 * 
 * If two results are equal, mark the test as a success. Otherwise, mark
 * the test as a failure.
 * 
 * @param lhs The value on the left-hand side of the equality test.
 * @param rhs The value on the right-hand side of the equality test.
 * @param ... Optional parameters, namely @li <span class="paramname">compare</span> The equality function, defaults to the naive
 *        <code>(lhs) == (rhs)</code>.
 *        @li <span class="paramname">msg</span> User-provided message shown upon failure, defaults to
 *        <code>testCase->name " FAIL: " str(lhs) != str(rhs)</code>.
 */
#define assertEqual(lhs, rhs, ...) concat(_assertEqual, COUNT_VARARGS(__VA_ARGS__)) (lhs, rhs, __VA_ARGS__)

/**
 * A composite of @c TestCase objects.
 *
 * Keeps track of useful metadata like success, failure count, etc.
 *
 * @invariant failures + skipped + errors <= tests
 * @invariant tests >= 0
 * @invariant interval >= 0.0
 */
typedef struct TestSuite {
    TestCase *first;
    TestCase *last;
    char *name; /**< TestSuite name, JUnit XML compliance sets this to
                   the filename. */
    int failures; /**< Number of failed TestCase objects. */
    int tests; /**< Number of TestCase objects in the suite. */
    int skipped; /**< Number of TestCase objects ignored. */
    int errors; /**< Number of TestCase objects with error results in
                   the suite. */
    struct timeval start;
    struct timeval stop;
    double interval; /**< The 'interval' is the time to run the test suite in milleseconds (no smaller than the sum of the intervals of the test cases). */
    struct TestSuite *next;
} TestSuite;

/**
 * Creates a @c TestSuite and adds it to the @c TestRunner.
 * 
 * Allocates memory for the <code>currentSuite</code> param, and
 * adds it to the ambient \ref g_runner test runner.
 * 
 * @b Important:
 * Must be the first thing called in the test init function before calling
 * <code>test(testCaseName)</code>.
 *
 * @param currentSuite A <code>TestSuite</code> pointer, expected to be NULL, but will be assigned to a newly allocated @c TestSuite object.
 */
#define suite(currentSuite)                       \
 { (currentSuite) = TestSuite_new(__FILE__); \
  TestRunner_add(g_runner, (currentSuite)); }

TestSuite* TestSuite_new(char *name);
void TestSuite_free(TestSuite *suite);
void TestSuite_run(TestSuite *suite);
void TestSuite_addTest(TestSuite *suite, TestCase *test);
void TestSuite_printXML(TestSuite *suite, FILE *xml);
void TestSuite_printToScreen(TestSuite *suite);

/**
 * A collection of <code>TestSuite</code>s.
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
