/**
 * @file
 * 
 * Lexical scanner for Core-ML.
 *
 * Responsible for reading an input stream, and producing @c core_Token
 * objects on demand (i.e., lazily).
 * 
 * @section coreGrammarSec Core-ML Grammar
 *
 * Recall in EBNF, we write <code>{rule}</code> for zero or more
 * instances of <code>rule</code> (right recursively, i.e.,
 * <code>{rules}</code> corresponds to the BNF rule
 * <code>&lt;opt-rules&gt;</code> defined as
 * <code>&lt;opt-rules&gt; = &lt;blank&gt; | &lt;rules&gt;</code>, where
 * <code>&lt;rules&gt; = &lt;rule&gt; &lt;rules&gt; | &lt;rule&gt;</code>
 * is the right-recursive expansion).
 * 
 * We also write <code>[rule]</code> for zero or one matches of
 * <code>rule</code>; roughly corresponding to the BNF rule
 * <code>&lt;opt-rule&gt; = &lt;blank&gt; | &lt;rule&gt;</code>.
 * 
 * The EBNF for the grammar is, so far:
 *
 * <pre>
 * literal = int | "True" | "False" ;
 * int = ? integer as sequence of digits ? ;
 * atomic-expr = var
 *             | literal
 *             | data-constructor
 *             | "(" expr ")" ;
 * expr = atomic-expr
 *      | abstraction
 *      | application
 *      | "let" value-def "in" expr
 *      | "letrec" value-def "in" expr
 *      | "case" "(" atomic-type ")" expr "of" var-binder
 *            "{" alternatives "}"
 *      | "if" bool-expr "then" expr "else" expr ;
 *
 * abstraction = "fn" var-binder "->" expr ;
 * var-binder = var "::" type ;
 * 
 * application = atomic-expr args ;
 * args = arg {arg} ;
 * arg = atomic-expr ;
 *
 * alternatives = alternative {";" alternative} ;
 * alternative = data-constructor {"@" type-binder} {var-binder} "->" expr
 *             | literal "->" expr
 *             | "_" "->" expr ;
 * type-binders = type-binder {type-binder} ;
 * type-binder = type-var
 *             | "(" type-var "::" kind ")" ;
 *
 * kind = atomic-kind
 *      | atomic-kind "->" kind ;
 * atomic-kind = "*"
 *             | "(" kind ")" ;
 * 
 * type = basic-type 
 *      | basic-type "->" type
 *      | "forall" type-binders "." type ;
 * basic-type = "Int" | "Bool"
 *            | atomic-type
 *            | type-application ;
 * type-application = basic-type atomic-type ;
 * atomic-type = type-var
 *             | type-constructor
 *             | "(" type ")" ;
 * 
 * definition = value-def
 *            | type-def ;
 * 
 * value-def = var "::" type "=" expr ;
 * 
 * type-def = "data" type-constructor {type-binder}
 *                "=" "{" constructor-defs "}"
 *          | "newtype" type-constructor type-constructor {type-binder}
 *                "=" type ;
 * constructor-defs = constructor-def {";" constructor-def} ;
 * constructor-def = data-constructor {"@" type-binder} atomic-types ;
 * atomic-types = atomic-type {atomic-type} ;
 *
 * 
 * program = definition {";" definition} ;
 * 
 * start = program ;
 * </pre>
 * 
 * @remark (1) The boolean (and the <code>if...then...else</code> expression)
 * are not necessary, since we can define them as algebraic data types
 * <code>data Bool = True | False;</code> and using pattern matching
 * <code>if c t f = case c { True -> t ; False -> f }</code>.
 *
 * @remark (2) This grammar is not LL(1) "on the nose", the @c type rule
 * experiences a small ambiguity similar to the "dangling optional else"
 * discussed in the Dragon book: there is no way to determine if the rule
 * matched is <code>basic-type</code> or <code>basic-type "->" type</code>
 * from the first token.
 * 
 * @author Alex Nelson <pqnelson@gmail.com>
 * @date November 10, 2018
 * @see https://downloads.haskell.org/~ghc/7.6.2/docs/html/users_guide/external-grammar-of-core.html
 */

#ifndef CORE_SCANNER_H_
#define CORE_SCANNER_H_

#include "core/token.h"

typedef struct core_Scanner {
    const char *start;
    const char *current;
    size_t line;
} core_Scanner;

/**
 * Constructs scanner for input buffer.
 *
 * Constructs a new @c core_Scanner that produces @c core_Token values
 * from the specified input source.
 *
 * @param source An input stream to be scanned.
 */
core_Scanner* core_Scanner_new(const char *source);

/**
 * Free @c core_Scanner object.
 *
 * This frees the memory allocated for @c this core_Scanner object, but
 * @em not for the input stream. Why? Because we might have lingering
 * core_Token objects still referencing the input stream.
 *
 * @param this The core_Scanner object to be freed.
 * @return nothing
 */
void core_Scanner_free(core_Scanner *this);

/**
 * Returns @c true if this scanner has another token in its input.
 *
 * When the scanner is at the end, it returns only @c false.
 * 
 * @param this The core_Scanner object being inspected
 * @return true if the scanner has another token
 */
bool core_Scanner_hasNext(core_Scanner *this);

/**
 * Produce the next token on demand.
 *
 * Finds and returns the next token from the scanner. When the scanner has
 * "finished", it will only produce EOF tokens.
 *
 * @param this The core_Scanner object in question.
 * @return A pointer to the next core_Token object.
 */
core_Token* core_Scanner_next(core_Scanner *this);

#endif /* CORE_SCANNER_H_ */
