# Maximally Multi-Focused Proofs for Skew Non-Commutative MILL

  Multi-focusing is a generalization of Andreoli's focusing procedure which allows the parallel application of synchronous rules to multiple formulae under focus. By restricting to the class of maximally multi-focused proofs, one recovers permutative canonicity directly in the sequent calculus without the need to switch to other formalisms, e.g. proof nets, in order to  represent proofs modulo permutative conversions. This characterization of canonical proofs is also amenable for the mechanization of the normalization procedure and the performance of further formal proof-theoretic investigations in interactive theorem provers.

  In this work we present a sequent calculus of maximally multi-focused proofs for skew non-commutative multiplicative linear logic (SkNMILL), a logic recently introduced by Uustalu, Veltri and Wan which enjoys categorical semantics in the skew monoidal closed categories of Street. The peculiarity of the multi-focused system for SkNMILL is the presence of at most two foci in synchronous phase. This reduced complexity makes it a good starting point for the formal investigations of maximally multi-focused calculi for richer substructural logics.

---

The file [code/Main.agda](https://github.com/niccoloveltri/multifocus-sknmill/blob/main/code/Main.agda) imports the whole development.  
The code typechecks using Agda version 2.6.2.
