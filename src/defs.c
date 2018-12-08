#include <stdint.h> // portable: uint64_t   MSVC: __int64 
#include "defs.h"

/* from https://stackoverflow.com/a/26085827 */
#if WINDOWS_PLATFORM
#include <windows.h>

// define DELTA_EPOCH_IN_MICROSECS
#if defined(_MSC_VER) || defined(_MSC_EXTENSIONS)
  #define DELTA_EPOCH_IN_MICROSECS  11644473600000000Ui64
#else
  #define DELTA_EPOCH_IN_MICROSECS  11644473600000000ULL
#endif /* defined(_MSC_VER) || defined(_MSC_EXTENSIONS) */

// windows version of gettimeofday()
int gettimeofday(struct timeval *tv, struct timezone *tz)
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
