# OCAML
## Introduction

This README provides an overview of the OCaml code. The code defines a simple language for Boolean expressions and programs, along with a lexer and parser for the language.

## Code Description

### Types

The code defines two primary types: `avar` (representing variables) and `bexp` (representing boolean expressions). Additionally, the `winstr` type is used to represent program structures.

### Boolean Expressions

The boolean expressions (`bexp`) can be constants (`Bcst`), variables (`Ava`), conjunctions (`And`), disjunctions (`Or`), or negations (`Not`).

### Program Structures

Program structures (`winstr`) include skip (`Skip`), assignments (`Assign`), sequence of instructions (`Seq`), if-else constructs (`If`), and while loops (`While`).

### Print Functions

The code provides functions (`bexpPrinter` and `winstrPrinter`) for printing boolean expressions and program structures in a readable format.

### Lexer and Parser

The code includes a lexer and parser for the language, allowing the conversion of input strings into abstract syntax trees (ASTs) representing programs. The lexer recognizes various tokens, such as boolean values, variables, and keywords. The parser constructs ASTs based on the recognized tokens.

### Anacomb - Lazy List-Based Parser Combinators for OCaml

Anacomb is a parser combinator library for OCaml that leverages the power of lazy lists to provide a flexible and expressive way of defining parsers. This README will guide you through the key concepts and features of Anacomb, as well as provide examples of usage.

### Lazy Lists in Anacomb

One notable feature of Anacomb is its use of lazy lists, implemented through the `inflist` type. Lazy lists allow for more efficient parsing, as only the necessary parts of the input are processed at each step. The `inflist` type is defined as follows:

```ocaml
type 'a inflist = unit -> 'a contentsil
and 'a contentsil = Cons of 'a * 'a inflist
```
Here, inflist represents a lazy list, and contentsil defines the structure of the list node. The inflist_of_string function is used to convert a regular string into an inflist.

```ocaml
let rec inflist_of_string s =
  let n = String.length s in
  let rec aux i =
    if i >= n then
      fun () -> raise Echec  (* Placeholder for end-of-list or failure *)
    else
      fun () -> Cons (s.[i], aux (i + 1))
  in aux 0
```

### Parser Combinators
#### Basic Parsers

Anacomb provides several basic parsers, including:

    terminal: Matches a specified terminal element in the input.
    terminal_cond: Matches a terminal element based on a provided condition.
    epsilon: Represents an empty or epsilon parser.

### Combining Parsers

Anacomb allows combining parsers using combinator functions:

    (-->): Sequential composition, applies one parser after another.
    (-|): Choice composition, tries the first parser, and if it fails, tries the second.
    star: Kleene star, repeats a parser zero or more times.

### Advanced Parsers with Results

Anacomb supports parsers that return results:

    terminal_res: Matches a terminal element and returns a result based on a provided function.
    (-+>): Sequential composition with result, applies one parser after another and combines their results.
    (++>): Sequential composition with results, applies one parser after another, passing results as arguments.


# Coq:
## Operational Semantics of WHILE Language

This repository contains an implementation of the operational semantics for the WHILE language using SOS (Small-Step Operational Semantics) rules and configurations. The code is written in Coq, a proof-assistant language.

## Overview

The implementation includes definitions for the WHILE language syntax, operational semantics rules, and proofs related to the language's small-step semantics. The key components are:

- **Syntax Definitions:**
  - Arithmetic expressions (`aexp`)
  - Boolean expressions (`bexp`)
  - WHILE language instructions (`winstr`)
  - Program state (`state`)

- **Semantic Functions:**
  - Evaluation of arithmetic expressions (`evalA`)
  - Evaluation of boolean expressions (`evalB`)

- **Small-Step Operational Semantics:**
  - SOS rules (`SOS_1`) for individual instructions
  - SOS configuration (`config`) to represent the execution state
  - SOS rules for the complete program (`SOS`)

- **Proofs:**
  - Proofs of progress and preservation for the WHILE language

## Code Structure

The main components of the code are organized as follows:

- `OperationalSemantics.v`: Contains the definitions of syntax, semantic functions, SOS rules, and proofs.
- `Examples.v`: Includes examples and test cases for the defined language and rules.

## Usage

1. **Coq Installation:**
   Ensure that you have Coq installed on your machine. You can download it from the official Coq website: [Coq](https://coq.inria.fr/download).

2. **Building and Running:**
   Use the Coq compiler to build and run the code. You can do this by running the following commands in your terminal:
   ```bash
   coqc OperationalSemantics.v
   coqc Examples.v
