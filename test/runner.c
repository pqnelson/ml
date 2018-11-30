#include <time.h>
#include <stdio.h>
#include <stdlib.h>
#include <stddef.h> /* offset_t */
#include <dirent.h>
#include <errno.h>
#include "defs.h"
#include "test.h"
#include "testsuites.h"
struct TestRunner *g_runner;

/**
 * As you write more test suites, append their initialization function here.
 */
void initTests() {
    initTokenSuite();
    initScannerSuite();
}

/**
 * For reasons I do not understand, Windows requires 29 characters (even
 * though the string is smaller than that).
 */
static const size_t ISO8601_STR_LEN = 29;
static const char xmlDir[] = "test-results";

/**
 * Writes the given time to an output string in ISO8601 format.
 *
 * @param time The given time to format
 * @param output A malloc'd buffer at least 29 characters big.
 */
void timeToIso8601(time_t time, char *output) {
    struct tm tm_info;
#if _WIN32
    localtime_s(&tm_info, &time);
#else
    localtime_r(&time, &tm_info);
#endif
    strftime(output, 29, "%Y-%m-%dT%H:%M:%S", &tm_info);
}

static void makeFilename(char **buf_p) {
    time_t rawtime = 0;
    struct tm tm_info = {0};
    time(&rawtime);
    // assert (rawtime != 0)
#if _WIN32
    localtime_s(&tm_info, &rawtime);
#else
    localtime_r(&rawtime, &tm_info);
#endif
    // assert (tm_info != {0})
    strftime(*buf_p, 48, "test-results/test-%Y-%m-%dT%H-%M-%S.xml", &tm_info);
}

static void customFilename(char **buf_p, const char *dirName, int dirNameLen,
                           const char *filePrefix, int filePrefixLen) {
    // REQUIRE (*buf_p) can hold 35 + dirNameLen + filePrefixLen characters
    
    /* copy the directory prefix */
    // size_t offset = strlen(xmlDir);
    // strncpy(*buf_p, xmlDir, offset);
    
    /* copy the file name prefix */
    // strncpy(*buf_p, "/test-", 6);
    // offset = offset + 6;

    /* add the datetime to the file name */
    // timeToIso86001(rawtime, (*buf_p) + offset)
    // offset = offset + 29;

    /* end the file name with the '.XML' file ending */
    // strncpy(*buf_p, ".xml", 4);
    // offset = offset + 4;
    
    /* be sure the file name is null terminated */
    // **buf_p = '\0'; // null terminate the string
}

static void printXMLResults() {
    char *filename = (char*)malloc(48);
    if (NULL == filename) {
        eprintf("Could not create string to hold XML file name\n");
        exit(EXIT_MALLOCERR);
    } else {
        makeFilename(&filename);
    }
    
    FILE *xml = fopen(filename, "w");
    if (NULL == xml) {
        eprintf("XML output file null, error %d, aborting\n", errno);
        exit(errno);
    }
    TestRunner_printXML(g_runner, xml);
    fclose(xml);
    free(filename);
}

static int countFailures() {
    int failCount = 0;
    TestSuite *suite = g_runner->first;
    while(NULL != suite) {
        failCount += (suite->failures) + (suite->errors);
        suite = suite->next;
    }
    return failCount;
}

/**
 * You don't need to touch the main function.
 *
 * @TODO add command line options to specify:
 *  - XML output only
 *  - print output only
 *  - what directory to create the output xml file
 *  - what the file name should be to print the xml
 */
int main() {
    g_runner = TestRunner_new();
    int failCount = 0;
    initTests();
    TestRunner_run(g_runner);
    printXMLResults();
    TestRunner_printToScreen(g_runner);
    failCount = countFailures();
    TestRunner_free(g_runner);
    if (failCount > 0) {
        eprintf("Failed %d tests\n", failCount);
    }
    return failCount;
}
