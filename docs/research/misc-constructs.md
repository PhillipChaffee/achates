# Which C constructs mpv's `misc/` uses

Measured from clang's JSON syntax tree (`clang -fsyntax-only -Xclang
-ast-dump=json`) run with each file's real flags from rmpv's
`compile_commands.json`. The 15 compiled files parse with clang 18 without
errors. The count below is 229 function bodies; it includes a few inline
functions from system headers, so treat the percentages as approximate.

| Construct | Functions using it |
| --- | --- |
| Function calls | 79% |
| Struct member access | 53% |
| Pointer casts between types | 48% |
| Array indexing | 20% |
| Initializer lists | 11% |
| `float` or `double` values | 9% |
| Compound literals | 7% |
| `goto` | 2% (5 functions) |
| `switch` | 1% (3 functions) |
| Atomics | 1% (3 functions) |
| Variadic argument reads, statement expressions, inline assembly | 0 |

Only about a dozen functions use no pointers, no struct members and no
`goto`. So a translator that handles only pure arithmetic covers almost
nothing: pointers, structs and calls are the core of the job, and a memory
model is unavoidable.

Clang accepts the GNU-flavoured source and resolves every type, macro and
implicit conversion, so Achates can take its input from clang and does not
need its own C parser.
