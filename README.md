## **Type Inference for a Subset of OCaml**


## Overview
This project implements an interpreter for a subset of OCaml, focusing on type inference and expression evaluation. The implementation includes a constraint-based type inference system and big-step operational semantics for evaluating expressions. 

The project is part of CAS CS 320: Principles of Programming Languages and is implemented in OCaml, adhering to the provided specification.

The interpreter supports a variety of language constructs, including literals, options, lists, pairs, variables, assertions, operators, let-expressions, and recursive functions. It performs type checking and evaluation while handling edge cases such as division by zero, assertion failures, and invalid comparisons.


## Features

- **Type Inference:** Implements a constraint-based type inference system to determine principal type schemes for expressions.
- **Expression Evaluation:** Evaluates expressions using big-step operational semantics, supporting a rich set of OCaml constructs.
- **Parsing:** Extends a partial parser to support the language's grammar, including operator precedence and associativity.
- **Error Handling:** Raises exceptions for division by zero, assertion failures, and invalid comparisons of function values.
- **Modular Design:** Organized within a Dune project, with core logic in interp3/lib/interp3.ml and utilities in lib/utils.

## Language Constructs
The language supports the following constructs, as defined by the grammar in the specification:

- **Literals:** Unit `(())`, booleans (`true`, `false`), integers, and floating-point numbers.
- **Options:** `None` and `Some e`, with matching constructs.
- **Lists:** Empty list (`[]`), cons (`e1 :: e2`), and list matching.
- **Pairs:** Pair creation (e1, e2) and pair matching.
- **Variables:** Variable references with polymorphic type schemes.
- **Annotations:** Type annotations (`(e : τ)`).
- **Assertions:** assert e and assert false.
- **Operators:** Arithmetic `(+, -, *, /, +., -., *., /., mod)`, comparisons `(<, <=, >, >=, =, <>)`, logical `(&&, ||)`, and list cons `(::)`.
- **Let-Expressions:** `let x = e1 in e2` and `let rec f = e1 in e2` for recursive functions.

Operator precedence and associativity are defined as follows (in increasing precedence):

- `||` (right)
- `&&` (right)
- `<, <=, >, >=, =, <>` (left)
- `::` (right)
- `+, -, +., -. `(left)
- `*, /, mod, *., /.` (left)
- Function application (left)

## Implementation Details

The implementation is divided into three main parts:

**Part 1: Parsing**

- Extends the provided parser in `interp3/lib/interp3.ml` to support the full grammar.
- Handles desugaring within the parser, mapping language constructs to the internal `expr` type.
- Accounts for operator precedence and associativity as specified.

**Part 2: Type Inference**

Implements the following functions for type inference:

- `principle_type : ty -> constr list -> ty_scheme option:` Computes the principal type scheme by finding the most general unifier for constraints and quantifying free variables.
- `type_of : stc_env -> expr -> ty_scheme option:` Determines the principal type scheme of an expression in a given context, returning None if no unifier exists.
- `is_well_typed : prog -> bool:` Checks if a program (a sequence of let-expressions) is well-typed by verifying each binding in the context of prior bindings.

The type inference system uses a constraint-based approach, with typing rules for:

- Literals (unit, booleans, integers, floats)
- Options (`None`, `Some`, matching)
- Lists (nil, cons, matching)
- Pairs (creation, matching)
- Variables (with substitution for polymorphic types)
- Annotations
- Assertions
- Operators (arithmetic, comparison, logical)
- Let-expressions (including recursive)

Fresh type variables are generated using the `gensym` function from the `Utils` module. The `VarSet` module is used for managing type schemes.

**Part 3: Evaluation**

Implements `eval_expr : dyn_env -> expr -> value `to evaluate expressions according to big-step operational semantics. Supported values include:

- Integers, floating-point numbers, booleans, unit
- Closures (for functions)
- Pairs, lists, and option values (`None`, `Some v`)

Evaluation handles exceptions:

- **DivByZero:** Raised for division or modulus by zero.
- **AssertFail:** Raised for failed assertions.
- **CompareFunVals:** Raised for polymorphic comparisons involving closures.

The semantics cover literals, options, lists, pairs, variables, annotations, assertions, operators, conditionals, function application, and let-expressions.

## Code Structure
The implementation resides in the following files:

- `interp3/lib/interp3.ml`: Core logic for parsing, type inference, and evaluation.
- `lib/utils/utils.ml`: Defines types (`ty`, `constr`, `stc_env`, `expr`, `value`, etc.) and utilities (`gensym`, `VarSet`).
- `examples.ml`: Contains test cases for validating the interpreter.

The project uses a `Dune build` system, with skeleton code provided in the repository.

## Setup and Installation

## Prerequisites:

- OCaml (version 4.14 or later)
- Dune (version 3.0 or later)
- Git


### 1. Clone the Repository:

``` bash
git clone https://github.com/jasonjiang/type-inference-ocaml.git
cd type-inference-ocaml
```

### 2. Build the Project:
``` bash
eval $(opam env)
dune build      
```


### 3. Run Tests:
``` bash
dune test  // To run test 
dune utop  // To test some features yourself
```
Note: Running examples.ml validates many test cases but does not guarantee correctness.


## Usage

To use the interpreter:

- Define programs using the supported grammar (see `examples.ml` for samples, e.g., `sum_of_squares`).
- Use `type_of` to infer the type scheme of an expression.
- Use `is_well_typed` to check if a program is well-typed.
- Use `eval_expr` to evaluate expressions and obtain values.

Example program:
```bash 
let sum_of_squares x y =
    let x_squared = x * x in
    let y_squared = y * y in
    x_squared + y_squared
let _ = assert (sum_of_squares 3 (-5) = 34)
```


## Contributing
Contributions are welcome! Please submit a pull request or open an issue for bugs, improvements, or feature requests. Ensure changes preserve the provided skeleton code and pass all tests.

## License
This project is licensed under the MIT License. See the LICENSE file for details.

## Acknowledgments

CAS CS 320: Principles of Programming Languages
Skeleton code and utilities provided by the course staff

