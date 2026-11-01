HEADLINE(s):
1 - This is a human-written and MUST NOT be touched by ANY agent for ANY reason beyond EXPLICIT PERMISSION.
2 - This is the ultimate source of truth for the project and every change must consult it to ensure the code or other docs are fully this-file compliant, so ANY drift must immediately pause the work and I should be communicated in detail what the blocker is and how to objectively best proceed.

DEFINITION(S):
1 - Kernel: `bend/bend2/bendtt.lean`: Unchanged and the source of truth.
2 - Bend: the language that the kernel gives a meaning to. Its code is a Book, as the kernel's `Book.parse` gives it. Its meaning is the kernel's `Eval`. Nothing more, nothing less. `.bend` text is a way to write Bend, through `bend -o`.
3 - Program: a Book with a def named `main` (no `main`: fail). `main` takes a list of bytes and gives a list of bytes, as values of these shapes (what `bend -o` gives for `base.bend`'s `List<Word(8)>`):
    - list: `(.Nil, ())`, or `(.Con, (byte, (list, ())))`.
    - byte: 8 bits, lowest first: `(.WCon, (bit, (rest, ())))` 8 times, then `(.WNil, ())`.
    - bit: `(.False, ())` is 0, `(.True, ())` is 1.
4 - Data form: how a kernel term or Book is written as a Bend value. Each term or Book has exactly one data form (the data form is a Lean function, not a `partial def`), and no two share one (a Lean theorem proves it). INVARIANTS #2 and #5 compare Lean and Bend through it.

GOAL(S):
1 - A PURE, SELF-HOSTING BEND COMPILER, WRITTEN IN BEND, THAT I CAN TRUST. GETTING THIS RIGHT FROM THE START IS AN ABSOLUTE MUST.
    - INPUT: A BEND BOOK (DEFINITION #2), ITS OWN BOOK INCLUDED.
    - PROMISE: THE COMPILED PROGRAM GIVES WHAT `Eval` GIVES (INVARIANTS #1).
    - PROOF: `--verdict` PROVES THE PROMISE ABOUT THE COMPILER'S OWN BOOK.
    - RUNNING IT: THE TRUST REACHES THE BINARY THAT RUNS ON THE PC. WE ACCEPT SLOWNESS, OR A BEND INTERPRETER-OR-COMPILER WRITTEN IN LEAN, ALONG THE WAY.
2 - IT CAN GROW: I CAN ADD OPTIMIZATIONS, FEATURES BEYOND BEND, NEW INTERNAL REPRESENTATIONS OR NEW TARGETS. THE LAW FOR BEND (INVARIANTS #1 AND #4) STAYS EXACTLY AS IT IS AND MUST STILL PASS `--verdict`. SO OUR COMPILER ALWAYS STAYS A PROVEN BEND COMPILER.
3 - TARGETS: OUR LAWS HOLD FOR ANY TARGET WHOSE MEANING IS WRITTEN IN BEND. THE FIRST TARGET IS WASM (WEBASSEMBLY): IT IS SMALL AND HAS AN OFFICIAL FORMAL SPEC. NATIVE MACHINE CODE HAS NO COMPACT FORMAL SPEC, AND C'S MEANING IS HUGE AND FULL OF UNDEFINED BEHAVIOR.

INVARIANT(S):
1 - FOR EVERY PROGRAM, NOT ONLY THE ONES THAT THE KERNEL ACCEPTS (SO WE NEED NO BEND COPY OF THE CHECKER): IF THE COMPILED PROGRAM, RUN BY ITS TARGET'S MEANING (THE TARGET'S BEND COPY, FOR EXAMPLE WASM'S: WHAT WE TRUST #6), GIVES A RESULT, IT IS THE RESULT THAT `Eval` GIVES (`Eval` GIVES AT MOST ONE RESULT, AFTER ONE NUMBER OF STEPS: A LEAN THEOREM PROVES IT). IF `Eval` GIVES A RESULT, THE COMPILED PROGRAM GIVES IT OR RUNS OUT OF MEMORY; WITH ENOUGH MEMORY (#4), IT ALWAYS GIVES IT. SO OUR COMPILER DOES NOT CHECK TYPES: A PROGRAM THAT THE KERNEL REJECTS MAY RUN FOREVER OR GET STUCK, AND ITS OWN LAWS HOLD ONLY AFTER `--verdict` ACCEPTS IT.
2 - THE BEND COPY OF `Eval`, WHICH THE LAWS OF STEP 1 USE, GIVES WHAT THE REAL ONE GIVES (EACH TERM AS ITS DATA FORM: DEFINITION #4), AFTER THE SAME NUMBER OF STEPS, IN BOTH DIRECTIONS (NO EXTRA RESULT, NO MISSING RESULT). A LEAN THEOREM PROVES IT.
3 - A RUN OF A PROGRAM (DEFINITION #3) STARTS AT `(main input)`, THAT IS `App Q1 (Ref "main") input`. THE LIST OF BYTES THAT IT GIVES IS ITS RESULT, AND #1 HOLDS FOR EVERY INPUT. IF `Eval`'S FINAL VALUE IS NOT A LIST OF BYTES, BOTH SIDES COUNT AS "NO RESULT".
4 - "ENOUGH MEMORY": EACH TARGET'S LAW FIXES A FORMULA F OF THE PROGRAM'S SIZE AND THE SIZE OF THE LARGEST TERM THAT `Eval` REACHES BEFORE IT GIVES THE RESULT (THE INPUT IS IN THE FIRST TERM). WITH AT LEAST F BYTES, THE COMPILED PROGRAM GIVES THE RESULT. THE COMPILER CAN'T CHOOSE F. WHEN F IS MORE THAN THE TARGET CAN HAVE (WASM: 4 GiB), THE LAW PROMISES NOTHING FOR THAT RUN.
5 - OUR COMPILER DOES NOT READ .bendtt TEXT. ITS INPUT IS THE BOOK THAT THE KERNEL'S OWN PARSER (`Book.parse`) GIVES FOR THAT TEXT, WRITTEN AS A LIST OF BYTES (DEFINITION #3) BY THE LEAN WRITER (NOT A `partial def`). FOR EVERY BOOK, THE BEND READER, WHICH THE LAWS OF STEP 1 USE, GIVES BACK EXACTLY THAT BOOK'S DATA FORM (DEFINITION #4) FROM THE BYTES THAT THE LEAN WRITER WRITES FOR IT. A LEAN THEOREM PROVES IT.

TRUSTED PIECE(S):
1 - Lean itself.
2 - The LEAN-VALIDATED, PROVEN-SOUND kernel (DEFINITION #1) is the definition of Bend. What it says a program computes IS what the program actually computes. IT IS FIXED: WE CANNOT TOUCH IT IN ANY WAY WHATSOEVER.
3 - From #2 follows that every proof in a Bend program that `--verdict` accepts is true (`--verdict` runs the kernel)
4 - The .bendtt text produced from a .bend file via `bend -o` means what said .bend file says.
5 - A WASM engine follows the WASM spec.
6 - Our Bend copy of WASM's meaning: only the part of WASM that our compiler uses, its binary format included. It is reviewed against the WASM spec and tested with the spec's official test suite. It is not proven, because we know of no Lean or Bend version of the spec. This is a named exception to WHAT WE DON'T TRUST #3.

UNTRUSTED PIECE(S):
1 - The current Bend compiler written in TypeScript.
2 - A checker result without --verdict.
3 - OUR OWN BOOTSTRAP CODE UNTIL IT'S SOMEHOW PROOF-VALIDATED.

STEP(S):
1 - We must write BEND LAWS IN BEND'S SYNTAX about >OUR OWN< compiler, so that `--verdict` proves that it is correct by the rules of `Eval`. This is because our compiler is Bend code, and a Bend proof can talk about it directly(a Lean proof could only reason about it from the outside).
2 - We must write a BEND INTERPRETER IN LEAN, with a Lean proof that it gives what `Eval` gives, so that we have a trusted way to RUN >OUR OWN< compiler (it runs any Bend program, ours included). This is because `Eval` is a list of rules, not a program (it can't run anything), we don't trust the current compiler, and our compiler can't run itself before it is compiled.
3 - We must write a LEAN PROOF THAT JOINS #1 AND #2: when the interpreter runs >OUR OWN< compiler, the bytes it writes follow the laws of #1 (it works for any Bend program and its laws, ours included). This is because #1 only says that the compiler is correct by the rules of `Eval`, and #2 only says that the interpreter follows `Eval`. Without this proof, nothing says that the laws hold for what actually runs on the PC.
4 - We must write the BEND COPY of `Eval` and the LEAN PROOF of INVARIANTS #2. This is because Bend can't use Lean's `Eval`, so #1 can only state its laws through a copy. Without this proof, a wrong copy makes #1 prove the wrong thing.
5 - We must write the BEND COPY OF WASM'S MEANING (WHAT WE TRUST #6), so that the laws of #1 can say what a compiled program gives. This is because our compiler compiles to WASM (OUR GOALS #3), and the WASM spec is not written in Bend.
6 - We must write the LEAN WRITER, the BEND READER and the LEAN PROOF of INVARIANTS #5. This is because the kernel's parser is made of `partial def`s, so no Lean theorem can say what it returns, and the kernel is fixed (WHAT WE TRUST #2): a Bend copy of the parser could never be proven to read a text as the kernel does. Without this proof, our compiler could compile a different book than the one the kernel read.
7 - We must write a LEAN VERSION OF THE OFFICIAL WASM SEMANTICS of the subset that our compiler uses, TRANSLATED BY A PROGRAM FROM THE SPEC'S OWN FORMAL SOURCE (SpecTec), and a LEAN PROOF that the Bend copy of WASM (#5) gives what it gives. This is because our Bend copy is only reviewed and tested (WHAT WE TRUST #6). With this proof we trust the spec's SpecTec source and the translator instead. The official tests of #5 stay, for historical reasons.

NOTE(S):
1 - The current UNTRUSTED TypeScript compiler is only a reference guide for ideas.
2 - PROOF QUALITY DOESN'T MATTER UNLESS PROOFS ARE SO SLOW THEY BLOCK. PROOFS DON'T TAKE PART IN REVIEW SWEEPS UNLESS I TELL YOU TO. LAWS AND THEOREMS (BEND AND LEAN), AND THE DEFINITIONS THEY USE, ON THE OTHER HAND, SHOULD ALWAYS BE DOUBLE-QUESTIONED TO ENSURE THEY REALLY REALLY MATCH MY INTENT; THEN THE LAWS AND THEOREMS ARE PROVEN. THIS DOES NOT MEAN OVERDO LAWS. WE WANT ENOUGH LAWS FOR THE COMPILER TO BE EXACTLY AS SAFE AS IT NEEDS TO BE, NOT MORE NOT LESS.
3 - THE COMPILED CODE KEEPS ITS STACK IN WASM MEMORY, NOT ON THE ENGINE'S CALL STACK. THE WASM SPEC LETS AN ENGINE STOP A PROGRAM WHEN THE ENGINE'S CALL STACK RUNS OUT, SO MEMORY MUST BE THE ONLY RESOURCE LIMIT (INVARIANTS #4).
4 - Bend guide may serve as reference; same as the untrusted compiler. Things like import dont seem to exist in the kernel for example so are out of scope and not needed for a bootstrap even if ir means a single huge file
5 - EFFECTS LATER: MODEL THEM AS PURE DATA (`main` GIVES REQUESTS, A HOST ANSWERS), SO `Eval` STILL GIVES THEM A MEANING.