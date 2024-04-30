# Artifact for "A concurrency model based on monadic interpreters"

## Overview

The code in this artifact contains two parts:

- `ctrees/`: custom version of the Choice Trees library
- `src/`: Coq code of the model presented in the paper


## Build instructions

Requirements: opam, the OCaml Package Manager (https://opam.ocaml.org/doc/Install.html)

```sh
git clone https://github.com/micro-vellvm-concurrency/micro-vellvm-concurrency.git
cd micro-vellvm-concurrency
opam update
opam switch create micro-vellvm-concurrency ocaml-base-compiler
eval $(opam env --switch=micro-vellvm-concurrency)
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install coq.8.18.0 coq-ext-lib.0.12.1 coq-itree.5.2.0 coq-mmaps.1.1 coq-relation-algebra.1.7.10
wget https://github.com/damien-pous/coinduction/archive/8300f80ac06fc22a76bb9e64d2817897790d7516.tar.gz
tar -xzf 8300f80ac06fc22a76bb9e64d2817897790d7516.tar.gz
opam pin coinduction-8300f80ac06fc22a76bb9e64d2817897790d7516
cd ctrees
dune build
cd ../src
coq_makefile -f _CoqProject -o Makefile
make
dune build # only for extracted OCaml code
```

This last command produces a binary `src/_build/default/main.exe` that runs the collecting interpreter on a few litmus tests.

## Results

Unlesse otherwise noted, the source files mentioned in this section are in `src/`.

### The model (Section 3)

- `Events.v`: signatures of the various events and branches (Figure 3).
- `Var.v`: interpretation of local and global variable accesses (Section 3.4)
- `Thread.v`: thread interleaving and interpretation of spawn events (Section 3.5)
- `PS.v`: Promising-like interpretation of memory accesses (Section 3.6)
- `lang.v`: the source language syntax (Sections 3.2 and 3.3, Figure 3)
- `Interp.v`: the interpretation stack (Section 3.1, Figure 2)
- `Thrd.v`: IR implementation of `thrd_create` and `thrd_join` from C11 (Section 3.2, Appendix A)

### Executability (Section 4)

- `Sched.v`: implementation of round-robin and random schedulers
- `Pick.v`: interpretation of undef as a random value
- `Examples.v`: example IR programs
- `main.ml`: OCaml implementation of a collecting interpreter

For convenience, the output from the collecting scheduler is in `output.txt` (generated in 150 seconds on a laptop).

### Transporting equivalences through the model (Section 5.1)

Theorem 1 corresponds to `interp_state_sbisim_eq`, L875 of `ctrees/theories/Interp/FoldStateT.v` The proof uses an alternative definition for CTree bisimilarity, defined in `ctrees/theories/Eq/SBisimAlt.v` and `ctrees/theories/Eq/SSimAlt.v`.

The proofs that relevant handlers are quasi-pure are in `Interp.v`, from line 224 to the end of the file.

The theorem stating that strong bisimulation can be transported through the interleaving stage is `interleave_sbisim`, line 702 of file `ThreadFacts.v`.

### An operational perspective on the model (Section 5.2)

The final theorem is `step_instr_interleave`, L830 of `LangStep.v`.

### Other models (Section 5.3)

- `SC.v`: sequentially consistent memory interpretation
- `TSO.v`: TSO memory interpretation

The simulation between the SC and TSO interpretations of memory accesses is in `TSO.v`, theorem `ss_sc_tso` (line 258).

The simulation between the SC and PS interpretations of memory accesses is in `PS.v`, theorem `ss_sc_ps` (line 1140).

## Axioms

There are no admitted theorems in our development.

We inherit from a technical issue from the `ctree` library: we had to `Unset Universe Checking` because some theorems from the CTrees library require it.
The issue stems from incompatible imports of libraries, notably the Interaction Trees and Relational Algebras ones. The root of the problem goes deep: Coq's standard library relies on so-called Template Polymorphisms for ubiqutous definitions such as the sum or product of types.
The problem is a fundamental one, that calls for changes on the Coq's theory itself (see: https://coq.zulipchat.com/#narrow/stream/237977-Coq-users/topic/Status.20of.20universe.20polymorphism.3F ), hence why this unsatisfactory situation stands at the moment.
Naturally, the soundness of our results are in no way challenged by this problem: exploiting a soundness leak by unsetting the universe checker locally for a development such as ours would require active malign action.

