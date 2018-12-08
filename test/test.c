/**
 * All the infrastructure for unit testing.
 *
 * This contains the boiler plate code for <code>TestCase</code>,
 * <code>TestSuite</code>, <code>TestRunner</code> functionality.
 *
 * 
 * @author Alex Nelson <pqnelson@gmail.com>
 * @date July 27, 2018
 * @see http://svn.apache.org/repos/asf/ant/core/trunk/src/main/org/apache/tools/ant/taskdefs/optional/junit/XMLJUnitResultFormatter.java
 */
/*
 * TODO: need to save the stdout, stderr to a string, and print that in
 * an appropriate XML element. This requires <code>dlsym()</code> to
 * hook the function with the element wrapping.
 * 
 * - http://pubs.opengroup.org/onlinepubs/009695399/functions/dlsym.html
 * - https://opensourceforu.com/2011/08/lets-hook-a-library-function/
 */
#include <stdlib.h>
#include <stdio.h>
#include <sys/time.h>
#include <time.h> /* localtime(), localtime_s() for MS */
#include <string.h>
#include "defs.h"
#include "test.h"

/**
 * @section sec Test Case
 *
 * We have a unit test described by a <code>TestCase</code> object.
 */
TestCase* TestCase_new(void (*run)(struct TestCase *this),
                       char *name,
                       char *classname) {
    TestCase *test = (TestCase *)malloc(sizeof(*test));
    if (NULL == test) {
        eprintf("Cannot allocate space for new test case '%s' in '%s'\n", name, classname);
        exit(EXIT_MALLOCERR);
    }
    test->run = run;
    test->name = name;
    test->classname = classname;
    test->result = TEST_RESULT_UNTESTED;
    test->next = NULL;
    return test;
}

void TestCase_free(TestCase *test) {
    if (!test) return;
    free(test);
    test = NULL;
}

#if defined(_WIN32) || defined(_WIN64) || defined(__CYGWIN__) || defined(__WIN32__) || defined(__TOS_WIN__) || defined(__WINDOWS__)
#include <Windows.h>
#include <stdint.h>
/**
 * This workaround is lifted shamelessly from StackOverflow, though
 * PostgreSQL has their own workaround too.
 * 
 * @see https://stackoverflow.com/a/26085827
 * @see https://git.postgresql.org/gitweb/?p=postgresql.git;a=blob;f=src/port/gettimeofday.c;h=75a91993b74414c0a1c13a2a09ce739cb8aa8a08;hb=HEAD
 */
static int ms_gettimeofday(struct timeval * tp, struct timezone * tzp)
{
    // Note: some broken versions only have 8 trailing zero's, the correct epoch has 9 trailing zero's
    // This magic number is the number of 100 nanosecond intervals since January 1, 1601 (UTC)
    // until 00:00:00 January 1, 1970 
    static const uint64_t EPOCH = ((uint64_t) 116444736000000000ULL);

    SYSTEMTIME  system_time;
    FILETIME    file_time;
    uint64_t    time;

    GetSystemTime( &system_time );
    SystemTimeToFileTime( &system_time, &file_time );
    time =  ((uint64_t)file_time.dwLowDateTime )      ;
    time += ((uint64_t)file_time.dwHighDateTime) << 32;

    tp->tv_sec  = (long) ((time - EPOCH) / 10000000L);
    tp->tv_usec = (long) (system_time.wMilliseconds * 1000);
    return 0;
}
#define mark_time ms_gettimeofday
#else
#define mark_time gettimeofday
#endif /* _WIN32 */

void TestCase_run(TestCase *test) {
    if (TEST_RESULT_UNTESTED == test->result) {
        mark_time(&(test->start), NULL); 
        test->run(test);
        mark_time(&(test->stop), NULL);
    }
}

/**
 * Print result to screen after running a test.
 * 
 * Only failures are printed to the screen.
 */
void TestCase_printToScreen(TestCase *test) {
    if (!test) return;
    else if (TestCase_isRunnable(test)) return;
    else if (TEST_RESULT_FAILURE == test->result) {
        eprintf("Test %s failed\n", test->name);
    }
    else if (TEST_RESULT_ERROR == test->result) {
        eprintf("Test %s error\n", test->name);
    }
}

/* For pretty printing XML to a file. */
static void indent(FILE *file, int layer) {
    while (layer-- > 0) fprintf(file, "  ");
}

/* Compare to XMLJUnitResultFormatter::endTest() for successful tests, and
 * XMLJunitResultFormatter::formatError() for errors, failures
 */
void TestCase_printXML(TestCase *test, FILE *xml) {
    if (NULL == xml) return;
    // assert(NULL != test);
    // assert(NULL != xml);
    indent(xml, 2);
    fprintf(xml, "<testcase name=\"%s\" classname=\"%s\" time=\"%f\"",
            test->name, test->classname, test->interval);
    if (TEST_RESULT_SUCCESS == test->result) {
        fprintf(xml, " />\n");
    } else {
        fprintf(xml, ">\n");
        indent(xml, 3);
        if (TEST_RESULT_FAILURE == test->result) {
            fprintf(xml, "\n");
        } else if (TEST_RESULT_SKIPPED == test->result) {
            fprintf(xml, "<skipped />\n");
        } else if (TEST_RESULT_ERROR == test->result) {
            fprintf(xml, "\n");
        } else if (TEST_RESULT_FAILURE == test->result) {
            fprintf(xml, "<failure>%s\n</failure>", test->message);
        } else {
            eprintf("Unknown result %d for test case %s\n",
                    test->result,
                    test->name);
        }
        indent(xml, 2);
        fprintf(xml, "</testcase>\n");
    }
}

/**
 * @section sec Test Suite
 * 
 * The design is for a simple, composite pattern --- a collection of
 * <code>TestCase</code> objects.
 */
TestSuite* TestSuite_new(char *name) {
    TestSuite *suite = (TestSuite *)malloc(sizeof(*suite));
    if (NULL == suite) {
        eprintf("No memory to allocate test suite %s", name);
        exit(EXIT_MALLOCERR);
    }
    suite->name = name;
    suite->errors = 0;
    suite->tests = 0;
    suite->skipped = 0;
    suite->failures = 0;
    suite->next = NULL;
    suite->first = NULL;
    suite->last = NULL;
    return suite;
}

void TestSuite_free(TestSuite *suite) {
    if (NULL == suite) return;
    TestCase *test;
    TestCase *next;
    test = suite->first;
    while (NULL != test) {
        next = test->next;
        TestCase_free(test);
        test = next;
    }
    free(suite);
    suite = NULL;
}

/**
 * Add a test case to a given suite.
 *
 * Ensures only non-null test cases belong to the test suite.
 *
 * @param suite The test suite which cases are added.
 * @param test Test case to add to the suite.
 */
void TestSuite_addTest(TestSuite *suite, TestCase *test) {
    if (NULL == suite && NULL != test) {
        eprintf("Trying to add test case \"%s\" to null suite\n",
                test->name);
    }
    if (NULL != suite && NULL == test) {
        eprintf("Trying to add null test case to suite \"%s\"\n",
                suite->name);
    }
    if (NULL == suite || NULL == test) return;
    // assert (NULL != suite)
    // assert (NULL != test)
    if (NULL == suite->first) {
        /* printf("suite %s adding new test %s\n", */
        /*        suite->name, test->name); */
        suite->first = test;
        suite->last = test;
    } else {
        suite->last->next = test;
        suite->last = test;
    }
    suite->tests++;
    // printf("TestSuite %s added test case %s\n", suite->name, test->name);
}
/**
 * Keep track of the number of failures, errors, skipped tests, and tests
 * run.
 */
static void TestSuite_updateStats(TestSuite *suite) {
    // assert every test case has been run
    TestCase *test = suite->first;
    while (NULL != test) {
        switch(test->result) {
        case TEST_RESULT_SKIPPED:
            suite->skipped++;
            break;
        case TEST_RESULT_FAILURE:
            suite->failures++;
            break;
        case TEST_RESULT_ERROR:
            suite->errors++;
            break;
        case TEST_RESULT_UNTESTED:
            eprintf("ERROR: suite '%s' test case '%s' untested, impossible\n",
                    suite->name, test->name);
            break;
        case TEST_RESULT_SUCCESS:
            break;
        }
        test = test->next;
    }
}

/*
 * Produces the interval between <code>stop</code> and
 * <code>start</code> timevals. In units of seconds, as doubles.
 */
#define timeit(x) ((double)((x)->stop.tv_usec - (x)->start.tv_usec)/1000000.0 \
                   + (double)((x)->stop.tv_sec - (x)->start.tv_sec))
/**
 * Run all the test cases in the suite, updating the interval for each test
 * case, then assigning the interval for the test suite.
 */
void TestSuite_run(TestSuite *suite) {
    if (NULL == suite) return;
    
    TestCase *test = suite->first;
    mark_time(&(suite->start), NULL); 
    while(NULL != test) {
        TestCase_run(test);
        test->interval = timeit(test);
        test = test->next;
    }
    mark_time(&(suite->stop), NULL);
    suite->interval = timeit(suite);
    TestSuite_updateStats(suite);
}

/* Compare to XMLJUnitResultFormatter::startTestSuite() and
 * XMLJUnitResultFormatter::endTestSuite() 
 */
void TestSuite_printXML(TestSuite *suite, FILE *xml) {
    // get the time in ISO format
    char isotime[40];
    time_t time = (suite->start).tv_sec;
    timeToIso8601(time, isotime);

    // print the test suite tag
    indent(xml, 1);
    fprintf(xml, "<testsuite name=\"%s\" errors=\"%d\" skipped=\"%d\" tests=\"%d\" time=\"%f\" timestamp=\"%s\">\n",
            suite->name, suite->errors, suite->skipped, suite->tests, suite->interval, isotime);

    // print all the test cases to XML
    TestCase *test = suite->first;
    while(NULL != test) {
        // assert(NULL != test)
        TestCase_printXML(test, xml);
        test = test->next;
    }
    // assert(NULL == test)
    
    // then close up the test suite tag
    indent(xml, 1);
    fprintf(xml, "</testsuite>\n");
}

void TestSuite_printToScreen(TestSuite *suite) {
    printf("Tests run: %d, Failures: %d, Errors: %d, Skipped: %d, Time elapsed: %f sec - %s\n",
    suite->tests, suite->failures, suite->errors, suite->skipped, suite->interval, suite->name);
}

/**
 * @section sec Test Runner
 * 
 * All code necessary for running through the test suites.
 */
TestRunner* TestRunner_new() {
    TestRunner* runner = (TestRunner*)malloc(sizeof(*runner));
    if (!runner) {
        eprintf("Cannot allocate space for new test runner!\n");
        exit(EXIT_MALLOCERR);
    }
    runner->first = NULL;
    runner->last = NULL;
    return runner;
}

void TestRunner_free(TestRunner *runner) {
    if (!runner) return;
    TestSuite *suite = runner->first;
    TestSuite *next;
    while(NULL != suite) {
        next = suite->next;
        TestSuite_free(suite);
        suite = next;
    }
    free(runner);
    runner = NULL;
}

/**
 * Add a @c TestSuite to the @c TestRunner.
 */
void TestRunner_add(TestRunner *runner, TestSuite *suite) {
    if ((NULL == runner) && (NULL != suite)) {
        eprintf("Trying to add suite \"%s\" to null runner\n",
                suite->name);
    }
    if (NULL == runner || NULL == suite) return;
    
    if (NULL == runner->first) {
        runner->first = suite;
        runner->last = suite;
    } else {
        runner->last->next = suite;
        runner->last = suite;
    }
}

/**
 * Run all the suites.
 */
void TestRunner_run(TestRunner *runner) {
    if (NULL == runner) return;
    
    TestSuite *suite = runner->first;
    while (NULL != suite) {
        // printf("TestRunner will run suite %s\n", suite->name);
        TestSuite_run(suite);
        suite = suite->next;
    }
}

void TestRunner_printToScreen(TestRunner *runner) {
    if (NULL == runner) return;
    
    TestSuite *suite = runner->first;
    while (NULL != suite) {
        TestSuite_printToScreen(suite);
        suite = suite->next;
    }
}

void TestRunner_printXML(TestRunner *runner, FILE *xml) {
    if (NULL == runner) return;
    if (NULL == xml) {
        eprintf("TestRunner_printXML() given a NULL xml file pointer\n");
        return;
    }
    fprintf(xml, "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n");
    fprintf(xml, "<testsuites>\n");
    TestSuite *suite = runner->first;
    while (NULL != suite) {
        TestSuite_printXML(suite, xml);
        suite = suite->next;
    }
    fprintf(xml, "</testsuites>");
}
