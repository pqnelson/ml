/**
 * System-independent definitions.
 *
 * We need to guarantee that booleans, etc., are well-defined even for
 * pre-C99 compilers. And here it is!
 *
 * Don't expose this to the children...
 * 
 * @author Alex Nelson <pqnelson@gmail.com>
 */
#ifndef DEFS_H
#define DEFS_H

/**
 * Print to the error stream.
 *
 * To print the errors to somewhere else, simply use <code>freopen()</code>
 * to use a different file for <code>stderr</code>.
 * 
 * @ref https://gcc.gnu.org/onlinedocs/gcc-4.4.7/cpp/Variadic-Macros.html
 */
#define eprintf(...) fprintf (stderr, __VA_ARGS__)

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
 * Boolean types are well-defined.
 */
#ifdef C99
#include <stdbool.h>
#else
typedef enum
{
	false = (1 == 0),
	true = (!false)
} bool;
#endif /* C99 */

/**
 * For use in computing the hash code of objects.
 */
typedef long hash_t;

#endif /* DEFS_H */
