#include <time.h>
#include <stdio.h>
#include <stdlib.h>
#include <stddef.h> /* offset_t */
#include <dirent.h>
#include <errno.h>
#include "utils.h"
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

static void customFilename(char *buf_p, const char *dirName, int dirNameLen,
                           const char *filePrefix, int filePrefixLen, time_t rawtime) {
    // REQUIRE (*buf_p) can hold 35 + dirNameLen + filePrefixLen characters
    
    /* copy the directory prefix */
    size_t offset = dirNameLen;
    strncpy(buf_p, dirName, offset);
    
    /* copy the file name prefix, i.e., "/test-" */
    strncpy(buf_p + offset, filePrefix, filePrefixLen);
    offset = offset + filePrefixLen;

    /* add the datetime to the file name */
    timeToIso8601(rawtime, buf_p + offset);
    offset = offset + 19;
    buf_p[offset-3] = '-'; // replace the "MM:SS" with "MM-SS"
    buf_p[offset-6] = '-'; // replace the "HH:MM" with "HH-MM"

    /* end the file name with the '.XML' file ending */
    strncpy(buf_p + offset, ".xml", 4);
    offset = offset + 4;
    
    /* be sure the file name is null terminated */
    buf_p[offset] = '\0'; // null terminate the string
}

static void printXMLResults(const char *xmlDir, const char *filePrefix, time_t rawtime) {
    size_t xmlDirLen = strlen(xmlDir);
    size_t filePrefixLen = strlen(filePrefix);
    size_t xmlSuffixLen = 4; // = strlen(".xml")
    size_t iso8601Len = 20; // really 19, but add one for good luck
    char *filename = malloc(xmlDirLen + filePrefixLen + xmlSuffixLen + iso8601Len + 1);
    if (NULL == filename) {
        eprintf("Could not allocate filename, bailing out!\n");
        TestRunner_free(g_runner);
        exit(EXIT_MALLOCERR);
    }
    customFilename(filename, xmlDir, xmlDirLen, filePrefix, filePrefixLen, rawtime);
    
    FILE *xml = fopen(filename, "w");
    if (NULL == xml) {
        perror("XML output file null?\n");
        eprintf("XML output file null, error %d, aborting\n", errno);
        free(filename);
        TestRunner_free(g_runner);
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
 */
int main() {
    time_t rawtime = 0;
    time(&rawtime);
    g_runner = TestRunner_new();
    int failCount = 0;
    initTests();
    TestRunner_run(g_runner);
    
    static const char xmlDir[] = "test-results";
    static const char filePrefix[] = "/test-";
    printXMLResults(xmlDir, filePrefix, rawtime);
    
    TestRunner_printToScreen(g_runner);
    failCount = countFailures();
    TestRunner_free(g_runner);
    if (failCount > 0) {
        eprintf("Failed %d tests\n", failCount);
    }
    return failCount;
}
