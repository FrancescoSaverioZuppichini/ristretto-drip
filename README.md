#Assignment 6 - Zuppichini Francesco
# Ristretto

This is a compiler for a small language called Ristretto, consisting of integer
and boolean expressions and statements, arrays, and functions.

## Drip

The compiler works by compiling from Ristretto ASTs to
IR trees which makes data layout explicit.

IR trees are translated to 3-address code.

## Perc

An optimizer can run on the 3-address code.

3AC is translated to x86 assembly code.

Lungo extends Ristretto with objects.
Lungo translates to IR trees also.


The language is based on the Xi language by Andrew Myers,
used in his compiler class at Cornell.

The design of the compiler is based on the MiniJava compiler
by Jens Palsberg. Each phase of the compiler has a concrete syntax
that can be used as input to the next phase. This makes it easier
to break the compiler up into digestable parts for a class.
In particular, it is not required that a previous phase of the compiler
be completely working for the next phase to be implemented.



