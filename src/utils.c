#include <stdint.h> // portable: uint64_t   MSVC: __int64 
#include "utils.h"

#if WINDOWS_PLATFORM
#include <windows.h>
#include <Windows.h>

/* from https://stackoverflow.com/a/26085827 */
// define DELTA_EPOCH_IN_MICROSECS
#if defined(_MSC_VER) || defined(_MSC_EXTENSIONS)
  #define DELTA_EPOCH_IN_MICROSECS  11644473600000000Ui64
#else
  #define DELTA_EPOCH_IN_MICROSECS  11644473600000000ULL
#endif /* defined(_MSC_VER) || defined(_MSC_EXTENSIONS) */

/* Also from https://stackoverflow.com/a/26085827 */
// windows version of gettimeofday()
int ms_gettimeofday(struct timeval *tv, struct timezone *tz)
{
    FILETIME ft;
    unsigned __int64 tmpres = 0;
    static int tzflag = 0;
    
    if (NULL != tv) {
        GetSystemTimeAsFileTime(&ft);
        
        tmpres |= ft.dwHighDateTime;
        tmpres <<= 32;
        tmpres |= ft.dwLowDateTime;
        
        tmpres /= 10;  // convert into microseconds
        
        // converting file time to unix epoch
        tmpres -= DELTA_EPOCH_IN_MICROSECS; 
        tv->tv_sec = (long)(tmpres / 1000000UL);
        tv->tv_usec = (long)(tmpres % 1000000UL);
    }

    if (NULL != tz) {
        if (!tzflag) {
            _tzset();
            tzflag++;
        }
        tz->tz_minuteswest = _timezone / 60;
        tz->tz_dsttime = _daylight;
    }
    
    return 0;
}

/**
 * This workaround is lifted shamelessly from StackOverflow, though
 * PostgreSQL has their own workaround too.
 * 
 * @see https://stackoverflow.com/a/26085827
 * @see https://git.postgresql.org/gitweb/?p=postgresql.git;a=blob;f=src/port/gettimeofday.c;h=75a91993b74414c0a1c13a2a09ce739cb8aa8a08;hb=HEAD
 */
int psql_gettimeofday(struct timeval * tp, struct timezone * tzp)
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
#endif /* WINDOWS_PLATFORM */

/**
 * For reasons I do not understand, Windows requires 29 characters (even
 * though the string is smaller than that).
 */
static const size_t ISO8601_STR_LEN = 29;

/**
 * Writes the given time to an output string in ISO8601 format.
 *
 * @param time The given time to format
 * @param output A <code>malloc</code>'d buffer at least 29 characters big.
 */
void timeToIso8601(time_t time, char *output) {
#if WINDOWS_PLATFORM
    struct tm tm_info;
    localtime_s(&tm_info, &time);
    strftime(output, ISO8601_STR_LEN, "%Y-%m-%dT%H:%M:%S", &tm_info);
#else
    struct tm *tm_info;
    tm_info = localtime(&time);
    strftime(output, ISO8601_STR_LEN, "%Y-%m-%dT%H:%M:%S", tm_info);
#endif
}
