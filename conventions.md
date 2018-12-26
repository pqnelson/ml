# Coding Conventions

- Code should be written in portable C99, and (hopefully)
  compiler-independent manner
- Global variables should be avoided. Only one global variable is used,
  and that's for unit testing. If using a global variable, prefix the
  identifier with `g_`.
- Pointer declaration (and function parameters which are pointers)
  should be of the form `type *identifier`, functions returning a
  pointer should be `type* function(...)`.
- **Design.** Code is organized into "modules" built around a data structure
  ("class") and a bunch of functions.
  - Header files will include a `typedef struct module_Class {...} module_Class`
    line, as well as any function prototypes.
  - Header files will include the `struct` definitions. Generically this
    is a "bad choice" for libraries, but since this is a self-contained
    programming with an eye towards pedagogy, it's not horrible.
- **Naming Conventions.** The heuristics used in function naming.
  - "Modules" are lowercased and consist of as few letters as possible
    (e.g., "test", "mml" for "Mini-ML", and so on)
  - "Classes" are PascalCased structs
  - "Functions" are camelCased names
  - The full name for a class is `module_ClassName`
  - The full name for a function is then
    `module_ClassName_functionName(Class *this, ...)` where the first
    argument is the object "acted upon"
  - **Static Functions.** "Private" helper functions are declared
    `static` (as is standard in C), but _may_ omit the `module_Class_`
    prefix. So, for example `static void myHelper(...)` or
    `static void indent()`. When it is a helper for a specific class, we
    _may_ include the `Class_` prefix for clarity (e.g., in `test/test.c` we
    use prefixes like in `static void TestSuite_updateStats(TestSuite *suite)` since several
    classes occur in the file; this is the exceptional situation).
  - **Enums:** we typedef enum definitions.
    Generically these will look like `typedef enum {MOD_ENUMERATOR = n,
    ...} MOD_EnumType`
    - The module prefix is now upper-cased for both the type name and
      the enumerator names.
    - The enumerator names are all uppercase and snake-cased
      (`WORDS_SEPARATED_WITH_UNDERSCORES`)
    - The type for the enum is PascalCased, so `MOD_EnumType` is the
      generic enum
- **Default Functions.** Classes generically will have the following
  functions:
  - `Class* Class_new(...)` to allocate memory for a `Class` object and
    initializes its fields
  - `void Class_free(Class *this)` will free up the memory for a `Class`
    object 
- **Nice Functions.** Useful functions which "most classes" have, but
  not necessarily all of them:
  - `bool Class_equals(Class *this, Class *rhs)` will compare `this`
    object with the `rhs` ("right hand side") object
    - This should be a transitive function, i.e., if `Class_equals(a, b)` 
      and `Class_equals(b, c)`, then `Class_equals(a, c)`
    - This should be symmetric, i.e., `Class_equals(a, b) == Class_equals(b, a)`
    - It should be reflexive: `Class_equals(a, a)` for all `a`
  - `hash_t Class_hashCode(Class *this)` will create a hashcode for a `Class`
    object. 
    - Contract: if `Class_hashCode(a) == Class_hashCode(b)`, then
      `Class_equals(a, b)` should return `true`.
  - `char* Class_toString(Class *this)` produces a _new_ string
    representation of the object `this`
- **Comments.** There are two types of comments in the program, namely
  Doxygen documentation comments and ACSL assertions. All the
  documentation comments are placed in header files, and all the ACSL
  contracts are placed in source files.

## Unit Testing

I've written a small library to do unit tests and write XML output. The
XML conforms to the JUnit schema, since I am specifically trying to be
"object oriented" in spirit...the tests surprisingly conform well to the
spec.

Writing a unit test is a 3-ish-step process:

**Step 0. Create a new file.** When unit testing the functions in
`src/mod/class.c` we create a file `test/mod/class_test.c`. The file should
schematically begin with:

```c
/* test/mod/class_test.c */
#include <stdlib.h>
#include <stdio.h>
#include <stddef.h>
#include "defs.h"
/* include "mod/class.h" */
#include "test.h" // for the test macros
#include "testsuites.h" // where prototype of the suite lives
```

**Step 1. Write the tests.** If we are
testing `int myFunction(...)`, create a void function `void
myFunctionTest1(TestCase *this)` which has at least one `assertEqual()`
statements. **Important:** the function must have its only parameter be
named `this`, to make the assert macros work as intended. (There is
probably some macro magic one can do to name the parameter whatever you
want, and update the `assertEquals()` macros, but this seemed like way
too much work for far too little reward.)

**Step 2. Create the Test Suite.** In `test/mod/class_test.c`, the last
thing we should do is create a function which schematically looks like:

```c
void initClassSuite() {
    TestSuite *currentSuite;
    suite(currentSuite); /* creates the "currentSuite" and adds it 
                            to the (global) test runner */
    TestSuite_addTest(currentSuite, test(myFunctionTest1)); /* add a test case to the suite */
    /* add all other tests to the suite similarly */
}
```

Since this is C, we need to prototype the function. So in the header
file `includes/testsuites.h`, add the function

```c
#ifndef TESTSUITES_H_
#define TESTSUITES_H_
// [other test suites omitted]

void initClassSuite(); // new test suite we add!

#endif /* TESTSUITES_H_ */
```

**Step 3. Add Test Suite to Test Runner.**
In `test/runner.c`, add `initClassSuite()` to the body of the 
`void initTests()` function. The test runner will automatically include
this suite, and the `main()` function will run them.

## Project Layout

The directory structure looks like:

```bash
ml
├───includes     # header files
│   └───mml      # Mini-ML intermediate language
├───src          # C files
│   └───mml      # Mini-ML intermediate language
├───target       # intermediate files
├───test         # unit tests
│   └───mml
├───test-results # XML output 
└───twelf        # twelf spec for languages
```
