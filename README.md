# Diagonal tilings and a triangular cellular automaton

This repository contains a four-page preprint and checked Lean proofs of six identities recorded in OEIS A401673 and A275667. The paper gives the combinatorial and algebraic arguments, a worked tiling example, and the correspondence with the formal definitions. [Read the preprint](preprint/preprint.pdf) · [LaTeX source](preprint/preprint.tex)

## Results

- On a fixed $2n\times 2n$ board there is one all-diagonal tiling and there are $n^2(n+1)$ tilings with exactly two ordinary dominoes. The second formula applies for $n\ge1$. [OEIS A401673](https://oeis.org/A401673) · [Lean proof](OeisProofs/Tilings.lean)
- For the single-seed odd-neighbour rule on triangular cells, the population satisfies $a(2t+1)=3a(t)$, $a(4t)=a(2t)$, $a(8t+2)=3a(4t)+4a(2t)$, and $a(8t+6)=3a(4t+2)+4a(2t)$ for every $t\ge0$. [OEIS A275667](https://oeis.org/A275667) · [Lean proof](OeisProofs/Automaton.lean)

## Reproduce the verification

With Lean's elan toolchain manager available, run the following commands at the repository root. The project pins Lean 4.36.0 and mathlib commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.

~~~sh
lake exe cache get
lake build
lake env lean Audit.lean
~~~

The audit reports only `propext`, `Classical.choice`, and `Quot.sound` for each of the six theorems. The tiling proof starts from row coverage and local pairing constraints. The automaton proof derives the three-neighbour update at each coordinate before counting the support.

## Independent enumeration

Run `python verify.py` with Python 3.10 or later. The program enumerates the two tiling counts at even side lengths from 2 to 12 and directly simulates the automaton through generation 255.

To rebuild the PDF, run `pdflatex preprint.tex` twice in the `preprint` directory.
