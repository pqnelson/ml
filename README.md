This is an exploration of various ways to implement an ML/Haskell-like
functional programming language. From scratch. In C. With an emphasis on
proving correctness of the implementation.

A generic functional programming language can be decomposed into several
levels based on abstraction:

- High level: this is what you program in, when you learn
  Haskell/OCaml/Standard ML
- Intermediate level: this is a reduced version of the programming
  language, types are filled in, some optimizations are made, and so on.
  It's still human readable at this point.
- Low Level: This is where the code is compiled into something
  resembling either assembly language or (binary) bytecode, specifically
  designed to run on a sort of virtual machine historically called
  an "abstract machine".

The compilation pipeline looks like:

``` haskell
ML.compile :: [ML.Expr] -> [CoreML.Expr]
CoreML.compile :: (AbstractMachine a) => [CoreML.Expr] -> [ByteCode a]

compile :: (AbstractMachine a) => [ML.Expr] -> [ByteCode a]
compile = CoreML.compile . ML.compile -- compile ML to bytecode

eval :: (AbstractMachine a, [ByteCode a]) -> (AbstractMachine a, [ByteCode a])
```

The low level abstract machine is the bit worth studying, where there
are actual substantive differences. Want a lazy language? It's done in
the abstract machine. Want to meddle with the garbage collector? Look in
the abstract machine. Native array support? Tinker with the abstract machine.

Lacking creativity, I'll generically refer to the "high level" language
as "ML" for "MetaLanguage", the intermediate level language as
"Core-ML", and the low level abstract machines...well, there are many
possibilities! This is more a study in functional programming language
implementation, so I hope to provide a number of abstract machine
implementations. 

## ML

We are trying to implement a _pure_ functional programming language. The
exact definition and criteria for a functional language to be "pure"
varies, unfortunately, it seems "safe" to say: "A functional language is
'pure' if all evaluation strategies (call-by-name, call-by-value,
call-by-need) produce 'the same results'."

(For more on pure functional languages, see Amr Sabry's "What is Purely
Functional Language?" _J. Functional Programming_ **8**, no.1 (1993):
1–22,
[doi:10.1017/S0956796897002943](https://doi.org/10.1017%2FS0956796897002943).)

Generic features one should expect:
- Functions are first class values
- Static typing via type inference
- Statically scoped
- Polymorphic types
- Type system includes support for Algebraic Data Types
- Garbage Collections

## Game plan for "Proving Correctness"

I'm hoping to use the [ACSL](https://frama-c.com/acsl.html) annotations
for "Hoare-triples in C". This is how we'll prove correctness.

We will use Twelf to prove the metatheory of the language is correct.
This is inspired from previous work in the field, specifically:

- Robert Harper and Daniel R. Licata,
  "Mechanizing Metatheory in a Logical Framework."
  [Eprint](https://web.archive.org/web/20160505171738/http://www.cs.cmu.edu/~rwh/papers/mech/jfp07.pdf)

"Mechanizing the metatheory" will prove the specification is correct
using Twelf, and ACSL will prove our implementation adheres to the
specification. (The skeptical reader may ask, "Isn't using Twelf to prove
the correctness of the specification simply punting the problem? It'd be
as correct as the Twelf implementation program, which may be buggy..."
True, but Twelf proofs can be checked "by hand", if needed.)

## Repository Layout

- `includes/` - All the header files
- `src/` - All the C code
- `target/` - All intermediate files that occur in the compilation
  process live here.
- `test/` - Unit tests live here.
- `test-results/` - XML output from running unit tests reside here.
- `twelf/` - Holds all the Twelf spec files

## FAQ

### Why are you doing this?

I need a functional programming language whose implementation has been
"proven correct".

### What License are you using?

MIT License for all the code.

