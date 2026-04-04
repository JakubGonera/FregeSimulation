This is an Isabelle formalisation of a theorem in the field of proof complexity.

# Summary
A Frege system is a propositional proof system that comprises a finite number of axiom schemes
and inference rules such that all inference rules are sound (if all premises are
true, then the conclusion is as well), and any formula that is implied from a set of
formulas has a proof in such a system (the system is implicationally complete).

In his 1976 PhD thesis [3], Robert Reckhow proved a well known result in proof complexity about polynomial simulation of Frege systems. The theorem states that any Frege system F1 can polynomially simulate another Frege system F2, that is, given a proof w in F2 there exists a polynomial time function f that translates this proof into a polynomial-size proof expressed in F1.

This repository contains the ongoing effort to formalise this result.

# Structure & Scope
This formalisation is in principle broken into two parts (following the proof by Krajicek [2]):
1. Simulation between two systems using De Morgan connectives (and, or, not)
2. The general case

Furthermore, this formalisation does not prove better subresults for specific cases as seen in Krajicek's (e.g. linearity of De Morgan simulation), but aims to prove the general polynomial length bound.

# References:
[1] Yuval Filmus. Reckhow’s theorem. Expository note, November 2010.\
[2] Jan Krajicek. Basic propositional logic, page 23–61. Encyclopedia of Mathematics and its Applications. Cambridge University Press, 1995.\
[3] Robert A. Reckhow. On the Lengths of Proofs in the Propositional Calculus.
PhD thesis, University of Toronto, Toronto, Ont., Canada, 1976. Department of Computer Science
