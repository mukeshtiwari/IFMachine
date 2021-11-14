Logical & Method
- predicate definitions
- arrays and iterated separated conjunction
- struct invariants
- ghost code?
- conditional heap chunks
- data types

C-features
- taking addresses of local/global variables, generally, reference operator
- heap and stack allocation, figure out timing of allocation
- recursive structs
- unions
- bit-precise reasoning, bit-casts
- parallel evaluation of arguments when order of evaluation is undefined in C
- support more C operators and language constructs (for, break, goto, ...)
- inlining of functions

Concurrency
- resources and locks, pthread spec

Refinement
- proper invariant attribution, generally match spec structure to program
- labels and specification bits attached to them

Maturity
- fix scanner not to regocnize spec keywords in C
- integer types, overflow checking
- type checking and error handling
- improve the parser, support comments (maybe use LALR generator)
- pretty printer
- C library specifications

Long Term
- integration with other tools
- see how much bi-abduction gives us
- invariant inference
- simple rewrite prover to bypass SMT and debug specifications
- eclipse integration?
- counterexample test cases for gdb
- temporal logic specifications, maybe related to declassification, too
- lock free volatile variables

Case studies
- consolidate examples
- test suite
- lots of small showcases
- a few non-security related case studies (linked lists, binary trees)
- CDDC with buffer
- simple mail server
- something practical