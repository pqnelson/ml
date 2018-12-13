/**
 * @file includes/mml/scanner.h
 * 
 * Lexical scanner for Mini-ML.
 *
 * Responsible for reading an input stream, and producing @c mml_Token
 * objects on demand (i.e., lazily).
 * 
 * @section subsection Mini-ML Grammar
 *
 * Recall in EBNF, we write <code>{rule}</code> for zero or more
 * instances of <code>rule</code> (right recursively, i.e.,
 * <code> {rules} = opt-rules </code> and <code>opt-rules = | rules</code>,
 * where <code>rules = rule rules | rule</code> is the right-recursive
 * expansion).
 * The EBNF for the grammar is, so far:
 *
 * <pre>
 * literal = int | "True" | "False" ;
 * int = ? integer as sequence of digits ? ;
 * atomic-expr = var
 *             | literal
 *             | "(" expr ")" ;
 * expr = atomic-expr
 *      | abstraction
 *      | application
 *      | "let" value-def "in" expr
 *      | "letrec" value-def "in" expr
 *      | "case" "(" aty ")" expr "of" vbind "{" alternatives "}"
 *      | "if" bool-expr "then" expr "else" expr ;
 *
 * abstraction = "fn" var-bind "->" expr ;
 * var-bind = var "::" type ;
 * 
 * application = atomic-expr args ;
 * args = arg | arg args ;
 * arg = atomic-expr ;
 *
 * alternatives = alternative ";" alternatives
 *              | alternative ";" ;
 * alternative = data-constructor type-binders var-binders "->" expr
 *             | literal "->" expr
 *             | "_" "->" expr ;
 * var-binders = var-binder var-binders | var-binder ;
 * type-binders = type-binder type-binders | type-binder ;
 * opt-type-binders = | type-binders ;
 * type-binder = type-var
 *             | "(" type-var "::" kind ")" ;
 * 
 * type = basic-type 
 *      | basic-type "->" type
 *      | "forall" type-binders "." type ;
 * atomic-type = type-var
 *             | type-constructor
 *             | "(" type ")" ;
 * basic-type = "Int" | "Bool"
 *            | atomic-type
 *            | type-application ;
 * type-application = basic-type atomic-type ;
 *
 * kind = atomic-kind
 *      | atomic-kind "->" kind ;
 * atomic-kind = "*"
 *             | equality-kind
 *             | "(" kind ")" ;
 * equality-kind = basic-type ":=:" basic-type ;
 * 
 * definition = value-def
 *            | type-def ;
 * 
 * value-def = var "::" type "=" expr ;
 *
 * type-def = "data" type-constructor opt-type-binders "=" constructor-defs
 *          | "newtype" type-constructor type-constructor opt-type-binders "=" type ;
 * constructor-defs = constructor-def constructor-defs
 *                  | constructor-def ;
 * constructor-def = data-constructor { "@" type-binder } atomic-types ;
 * atomic-types = atomic-type atomic-types | atomic-type ;
 * program = definition ";" | definition ";" program ;
 * 
 * start = program ;
 * </pre>
 * 
 * @remark The boolean (and the <code>if...then...else</code> expression)
 * are not necessary, since we can define them as algebraic data types
 * <code>data Bool = True | False;</code> and using pattern matching
 * <code>if c t f = case c { True -> t ; False -> f }</code>.
 * 
 * @author Alex Nelson <pqnelson@gmail.com>
 * @date November 10, 2018
 * @see https://downloads.haskell.org/~ghc/7.6.2/docs/html/users_guide/external-grammar-of-core.html
 */

#ifndef MML_SCANNER_H_
#define MML_SCANNER_H_

#include "mml/token.h"

typedef struct mml_Scanner {
    const char *start;
    const char *current;
    size_t line;
} mml_Scanner;

mml_Scanner* mml_Scanner_new(const char *source);
void mml_Scanner_free(mml_Scanner *this);

bool mml_Scanner_hasNext(mml_Scanner *this);
mml_Token* mml_Scanner_next(mml_Scanner *this);

#endif /* MML_SCANNER_H_ */
