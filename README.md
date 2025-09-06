# CYaRonC

CYaRonC is a compiler for the CYaRon! programming language. It translates CYaRon! source code into LLVM Intermediate Representation (IR).

## Features

CYaronC implements a extended version of the CYaRon! programming language, originally proposed in [Luogu P3695](https://www.luogu.com.cn/problem/P3695).

*   Static typing with `int` and `float` types.
*   One-dimensional arrays with custom, inclusive index ranges.
*   Standard input and output operations.
*   C-style expressions with arithmetic, comparison, and bitwise operators.
*   `ihu`, `hor`, and `while` control flow statements with a unique syntax.
*   Generation of LLVM IR, which can be executed directly via a JIT compiler or compiled to a native executable.
*   Support for debug information generation using the `-g` flag for use with debuggers like GDB or LLDB.

## Extended Syntax (Compared to Original Problem)

This implementation adds several features to the original CYaRon! language:

*   **Data Types**:
    *   A `float` type for 64-bit floating-point numbers (C's `double`).
    *   Arrays can be of type `float` (e.g., `array[float, 1..10]`).

*   **Operators and Expressions**:
    *   **More Arithmetic Operators**: Added `*` (multiplication), `/` (division), and `%` (modulo).
    *   **Bitwise Operators**: Added `&` (AND), `|` (OR), and `^` (XOR) for integers.
    *   **Unary Operators**: Supports unary `+` and `-` (e.g., `:set x, -5`).
    *   **Operator Precedence**: Standard C-style operator precedence is applied.
    *   **Parentheses**: `()` can be used to enforce a specific order of evaluation.
    *   **Complex Array Indices**: Array indices can be any valid integer expression (e.g., `arr[my_array[a*2 + b] + 1]`).
    *   **Type Promotion**: Integers are automatically promoted to floats in mixed-type expressions.
    *   **Less strict whitespace rules**: Four-space indentation is not required.

*   **Statements**:
    *   `:input`: A new statement to read a number from standard input into a variable.

*   **General**:
    *   **Comments**: Lines starting with `#` are treated as comments.
    *   **Variable Names**: Identifiers can contain letters, numbers, and underscores (`_`), as long as they don't start with a number.

## Building the Compiler

You will need `cmake`, a C++20 compatible compiler (like `clang` or `gcc`), and `llvm` installed.

```bash
# Create a build directory
mkdir -p build && cd build

# Configure and build the project
cmake -DCMAKE_BUILD_TYPE=Release ..
make
```

## Compiler Usage

### 1. Compile to LLVM IR

Use the `cyaronc` executable to compile a `.cyaron` source file into a `.ll` LLVM IR file.

```bash
# Syntax
./cyaronc [-g] <input.cyaron> <output.ll>

# Example
./cyaronc example/segment_tree.cyaron output.ll

# Example with debug symbols
./cyaronc -g example/segment_tree.cyaron output.ll
```
*   The optional `-g` flag adds debug information to the LLVM IR.

### 2. Execute the Code

You can run the generated LLVM IR in several ways:

```bash
# 1. Interpret the LLVM IR directly using lli
lli output.ll

# 2. Compile the LLVM IR to a native executable using clang
clang output.ll -o my_program

# Run the executable
./my_program

# 3. Compile with debug symbols and use a debugger
clang -g output.ll -o my_program_debug
lldb ./my_program_debug
```

## Language Syntax

### Comments

Comments start with a `#` and continue to the end of the line.

```cyaron
# This is a comment.
```

### Variables

All variables must be declared in a `{vars ...}` block at the top of the file. Variables are initialized to zero by default.

```cyaron
{ vars
    my_int: int
    my_float: float
    my_array: array[int, 1..10]
}
```

#### Types

*   `int`: A 64-bit signed integer, same as `long long` in C.
*   `float`: A 64-bit floating-point number, same as `double` in C.
*   `array[<type>, <start>..<end>]`: A one-dimensional array of `int` or `float` with an inclusive index range from `<start>` to `<end>`.

### Statements

#### Output: `:yosoro`

Prints the value of an expression to standard output, followed by a space.

```cyaron
:yosoro 123          # Prints "123 "
:yosoro my_int + 5   # Prints the result of the expression and a space
```

#### Assignment: `:set`

Assigns a value to a variable or an array element.

```cyaron
:set my_int, 100
:set my_array[1], 200
:set my_int, my_int + my_array[1]
```

#### Input: `:input`

Reads a number from standard input and stores it in a variable or array element.

```cyaron
:input my_int
:input my_array[5]
```

### Control Flow

Control flow statements use a block structure defined by `{...}`.

#### Comparison Operators

The following operators are used in all control flow statements:
*   `lt`: Less than (`<`)
*   `gt`: Greater than (`>`)
*   `le`: Less than or equal to (`<=`)
*   `ge`: Greater than or equal to (`>=`)
*   `eq`: Equal to (`==`)
*   `neq`: Not equal to (`!=`)

#### If Statement: `{ihu ...}`

The `ihu` statement executes a block of code if a condition is true. There is no `else` branch.

```cyaron
# Syntax: {ihu <op>, <expr1>, <expr2> ... }

{ihu eq, my_int, 10
    :yosoro 1
}
```

#### For Loop: `{hor ...}`

The `hor` statement creates a loop that iterates over an inclusive range. The loop variable must be an integer.
When the loop ends, the loop variable is set to the end value.

```cyaron
# Syntax: {hor <var>, <start_expr>, <end_expr> ... }
# Loops from start_expr to end_expr (inclusive).

{hor i, 1, 5
    :yosoro i  # Prints "1 2 3 4 5 "
}
```

#### While Loop: `{while ...}`

The `while` statement executes a block of code as long as a condition is true.

```cyaron
# Syntax: {while <op>, <expr1>, <expr2> ... }

:set i, 1
{while le, i, 3
    :yosoro i  # Prints "1 2 3 "
    :set i, i + 1
}
```

### Expressions

#### Operators

*   **Arithmetic**: `+`, `-`, `*`, `/`, `%` (modulo)
*   **Bitwise**: `|`, `&`, `^` (only operate on integers)

#### Type Promotion

In an expression involving both `int` and `float` types, integers are automatically promoted to floats for the calculation. The result will be a `float`.

```cyaron
:yosoro (5 + 0.5)  # Prints "5.500000 "
```

#### Precedence

Use parentheses `()` to group expressions and enforce a specific order of evaluation.

```cyaron
:yosoro (2 + 3) * 4  # Prints "20 "
```

## Running Tests

The test suite requires `lli` to be in your system's `PATH`.

```bash
python3 test/run_tests.py
```

## Examples

Examples can be found in the `example` directory.

1. [Segment Tree](example/segment_tree.cyaron)
    * A simple segment tree implementation. Solution to [Luogu P3372](https://www.luogu.com.cn/problem/P3372).