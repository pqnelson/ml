/**
 * @file includes/defs.h
 * 
 * System-independent definitions.
 *
 * We need to guarantee that booleans, etc., are well-defined even for
 * pre-C99 compilers. And here it is!
 *
 * Don't expose this to the children...
 * 
 * @section sec Exit Codes
 *
 * We have "standardized" exit codes, depending on what errors occur.
 * (Success is always <code>EXIT_SUCCESS</code>, quite boring.)
 *
 * The codes are compliant with the @c <sysexits.h> header file, we just
 * specify the errors more explicitly. For example, instead of
 * @c EX_OSERR for when @c malloc() returns a null pointer, we simply
 * define @c EXIT_MALLOCERR for that error (whose value coincides with
 * @c EX_OSERR since such a failure is a specific instance of an OS error).
 *
 * @see https://www.freebsd.org/cgi/man.cgi?query=sysexits
 * 
 * @author Alex Nelson <pqnelson@gmail.com>
 */
#ifndef DEFS_H
#define DEFS_H

/**
 * Print to the error stream.
 *
 * The same as @c printf but specifically to the @c stderr output stream.
 *
 * @TODO Make this print always to the output stream with file descriptor 2?
 * @see https://gcc.gnu.org/onlinedocs/gcc-4.4.7/cpp/Variadic-Macros.html
 */
#define eprintf(...) fprintf (stderr, __VA_ARGS__)

/**
 * @cond DEV
 */
/* {@see https://stackoverflow.com/a/2115886} */
#if defined(__STDC__)
# define C89
# if defined(__STDC_VERSION__)
#  define C90
#  if (__STDC_VERSION__ >= 199409L)
/* Apparently this was a "thing" */
#   define C94
#  endif /* (__STDC_VERSION__ >= 199409L) */
#  if (__STDC_VERSION__ >= 199901L)
#   define C99
#  endif /* (__STDC_VERSION__ >= 199901L) */
# endif /* defined(__STDC_VERSION__) */
#endif /* defined(__STDC__) */
/**
 * @endcond
 */

/**
 * Boolean types are well-defined.
 *
 * For C99 compliant compilers, this defaults to including the @c <stdbool.h>
 * header. We implement an @c enum version for pre-C99 compilers.
 */
#ifdef C99
#include <stdbool.h>
#else
/**
 * This definition of @c bool is taken from Donald Knuth.
 */
typedef enum {
    false = (1 == 0),
    true = (!false)
} bool;
#endif /* C99 */

/**
 * For use in computing the hash code of objects.
 *
 * I know that having a <code>_t</code> suffix is "bad form", but still...
 */
typedef long hash_t;

/**
 * File reading/writing error status.
 */
#define EXIT_IOERR 74
/**
 * Malloc returns @c NULL pointer.
 */
#define EXIT_MALLOCERR 71
/**
 * Handle bad input from user.
 *
 * Example: runaway comments, malformed input, etc.
 *
 * This coincides with @c <sysexits.h> value for @c EX_DATAERR.
 */
#define EXIT_BAD_INPUT 65


#endif /* DEFS_H */
