# MCML

## Introduction

I personally love the core ML programming language but implementing an ML is no easy task for the layperson, largely due to the complexities around type inference. Hence I have created this repository as a foundation for others to build upon. The entire code base including an editor with graphical throwback of inferred types (via WPF tooltips) weighs in at just over 1kLOC of F# code.


## Notes

The language implemented by this interpreter is a simple ML dialect featuring:

* Ints
* Chars
* Strings
* Tuples
* Arithmetic and boolean operators
* Functions
* Pattern matching
* Type inference with automatic generalization

The most notable missing features are:

* Exceptions
* Mutation

The design might appear peculiar so let me explain some of my goals. The objective is to turn this into a minimal bootstrapped ML compiler. This ML doesn't feature an exception mechanism so I have avoided exceptions in this code base in anticipation of it being translated into its own language. Hence the excessive use of the Result monad.

The interpreter was prone to stack overflows when interpreting code that makes many nested calls so I used a trampoline computational workflow to avoid stack overflows.


## Further work

Retrospectively, the interpreter should just be written in continuation passing style directly rather than using a computational workflow.

Error messages are sometimes bad because I have been naughty and used pattern matching directly in bits of the parser when I should have disciplined myself to use combinators for everything in order to have parse errors handled consistently.

The type checker should verify coverage in all pattern matches. If this were done it could reject programs with incomplete pattern matches, allowing the interpreter to run without the Result monad.
