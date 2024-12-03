# Slice

A language for cake-cutting.

## Getting started

### Requirements

The language OCaml, and its package manager, opam, are required. The OCaml version used is 5.1.1.
The following opam packages are also required:
dune 3.14.2, menhir 20231231, and z3 4.12.6.

Once opam is installed, the opam packages can be installed with the following command:
```
opam install [package.version]
```
Following this, enter the main Slice directory and run
```
eval $(opam env)
```
followed by
```
dune build
```
to build the source.

Our included scripts require Z3 as well.


## Writing Slice programs

The Slice syntax is functional in style, somewhat like OCaml (not as polished). While our papers inform on the core language, the surface language differs for an easier writing experience. To get a feel for how Slice programs are written, see the `examples/` folder.

### Cake-cutting primitives

#### Divide
`divide(interval, point)` splits `interval` into two intervals at `point`.

#### Eval
`eval(a, piece)` gives agent `a`'s value of `piece`.

#### Mark
`mark(a, interval, value)` gives a point in `interval`, say `r`, such that the value (according to agent `a`) of the interval from `interval`'s left endpoint to `r` is `value`. That is, if `l` is `interval`'s left endpoint, then the value of `[l,r]` is `value` according to agent `a`.

There are two versions of this primitive, `mark` and `markw`. The first takes in a value having type `Value`, while the second takes in a value having type `Real`. The second converts to the first by multiplying the real `value` by the output of `eval(a, interval)`.

#### Piece
`piece(i1, i2)` forms a piece out of `i1` and `i2`. In general, `piece` can take as input a list of intervals rather than just two.


### Type system considerations
Slice exhibits a linear-style type system that restricts the use of intervals and pieces being 'consumed' more than once. When a variable having type piece or interval needs to be passed to mark or eval, a `read` should be placed in front of it. Intuitively, this declares the purpose of the variable as 'read-only', so it is not counted as being consumed. For all other uses however, placing a `read` in front will throw a type error, so otherwise, the piece or interval can be used only once.

### Classic example: I cut, you choose

To illustrate how to write a Slice program, consider the following protocol for two agents, known as I cut, you choose:
One agent cuts the cake into two equally preferred pieces. The other agent picks their preferred piece of the two. The latter agent receives their pick, while the former agent receives the remaining piece.

This can be expressed as the following Slice program:
```
let ck = cake in
let (i1, i2) = divide (ck, markw (1, read ck, 1 / 2)) in
            if ((eval (2, read i2)) >= (eval (2, read i1))) then
                 (piece i1, piece i2)
            else
                (piece i2, piece i1)
```

The first line assigns the variable `ck` to the whole cake.
The second line consists of agent 1's actions, while the remaining part of the program asks agent 2 which piece they prefer, and then allocates accordingly.

The first line is required to assign the cake a variable, so that it can be 'read' by markw and also be divided in, both in line 2. The return type of this program is `piece x piece`. Agent 1 receives the first component while agent 2 receives the second.

### Notable surface language features

#### Comments

Slice allows comments much like OCaml:
```
(* Comment here! *)
```
There is no restriction on the span of lines they can take.

#### Abbreviations
While Slice does not support functions, abbreviations can be used to reduce repetitive code. When Slice translates from the surface language to the core language, it will replace any abbreviations with the underlying code.

Abbreviations are typically written in a separate file, which is also passed to Slice. The format for an abbreviation `foo` is the following:
```
def foo arg1 arg2 =
    bar
```
where `arg1` and `arg2` are the arguments for the abbreviation and `bar` is its body. To use the abbreviation `foo` in a program, simply put `foo(arg1, arg2)` in place of its body in the program. Abbreviations can also use abbreviations, as long as the ones used are found earlier in the file they are written in.

Example and common abbreviations can be found in `examples/abb.prtcl`.

#### Let-binding pattern matching
When an expression is a tuple type, the let binding can capture each tuple element individually. For example,
```
let (left, right) = foo in bar
```
where `foo` has type `A x B`, will bind the left element output by `foo` to `left` and the right element output by `foo` to `right` in the body `bar`. Slice *should* also be able to match on nested tuples.

### Implemented protocols

This artifact contains all known cake-cutting protocols implemented in Slice, divided between the following files: `table1/`, `table2/`, `wmh4/`, `type_examples/`. The protocols consist of all the protocols originally developed in Slice, as well as two new envy-free protocols, Aziz-Mackenzie-3 and Waste-Makes-Haste-4, and some other protocols used for testing purposes. The syntax of the original protocols have been slightly modified to accommodate our type system, though these changes are minimal. The file `abb.prtcl` consists of snippets of code that are commonly used within our protocols so that the protocols themselves can have these snippets abbreviated.

If desired, new protocols can be created by following the near ML style syntax shown in the examples. The below tools can be applied to any new protocols without additional difficulty.


## Verifying Slice programs

We refer to protocol properties that describe an allocation or its properties as allocation properties. Allocation properties of protocols can be determined to hold or not through Slice. The typical allocation property to verify is envy-freeness, but in principle, Slice can verify any allocation property.

Slice verifies slice programs by producing an SMTLIB file that captures what holds about your program.
To produce the SMTLIB file, (which is called `solve.smt2`), run the following command
```
dune exec exec/solver.exe [ABBREVIATIONS FILE] [PROTOCOL FILE] [ADDITIONAL ARGUMENTS]
```
where additional arguments could be
```
envy
```
This file gives the fastest envy-freeness verification.
```
envy_no_red
```
This produces an equivalent file to the previous command, but the formulas are not reduced to linear real arithmetic. These files may be more readable.
```
custom
```
This is for custom allocation properties written by the user.

### Writing custom allocation properties

As stated above, allocation properties are protocol properties describing the allocation of the protocol. Thus these can only describe the allocation of a protocol. To write custom allocation properties, interaction with Slice's source is required. Specifically, the OCaml function `custom: int -> term -> formula` located in `src/properties.ml` is the function to be modified to write a custom allocation property. For guidance on how to write a proper formula, see the rest of the code in `src/properties.ml` as well as `src/formula.ml` for term and formula syntax trees.

## Further interaction with Slice

All further interaction with Slice requires working within the source. For example, customizing the SMTLIB output of Slice (for the moment) requires modification of `src/solve.ml` and `exec/solve.ml`. However, it is quite convenient to work with the source using an OCaml top-level environment for experimentation.

## Included scripts

Some scripts are included in `testing/scripts/` for verifying envy-freeness and type-checking Slice programs. See this folder for more information.

## See our publications!

- [Introducing the Slice language (PLDI 2023)](https://arxiv.org/abs/2304.04642)

- [Faster verification, and piece-restrictive type system (CAV 2024)](https://arxiv.org/abs/2405.14068)
