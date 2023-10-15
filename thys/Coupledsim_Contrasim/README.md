# Coupled Similarity and Contrasimilarity, and How to Compute Them

*Coupled similarity* and *contrasimilarity* are nice semantic equivalences for systems with internal behavior.
This repository contains an [Isabelle2](https://isabelle.in.tum.de/index.html) formalization for the two with a focus
on game characterizations. The theory accompanies the publications [“Computing Coupled Similarity”](https://doi.org/10.1007/978-3-030-17462-0_14)
(Bisping & Nestmann, TACAS 2019) and [“A Game Characterization for Contrasimilarity”](https://doi.org/10.4204/EPTCS.339.5)
(Bisping & Montanari, EXPRESS/SOS 2021).

- Document: <https://luisamontanari.github.io/ContrasimGame/Unsorted/Coupledsim_Contrasim/document.pdf>
- Browsable theory: <https://luisamontanari.github.io/ContrasimGame/Unsorted/Coupledsim_Contrasim/index.html>

## Authors

- [Benjamin Bisping](https://github.com/benkeks) | <https://bbisping.de>
- [Luisa Montanari](https://github.com/luisamontanari)

## Abstract

We survey and extend characterizations of *coupled similarity* and *contrasimilarity* and prove properties relevant
for algorithms computing their simulation preorders and equivalences.

Coupled similarity and contrasimilarity are two weak forms of bisimilarity for systems with internal behavior.
They have outstanding applications in contexts where internal choices must transparently be
distributed in time or space, for example, in process calculi encodings or in action refinements.

Our key contribution is to characterize the coupled simulation and contrasimulation preorders by *reachability games*.
We also show how preexisting definitions coincide and that they can be reformulated using *coupled delay simulations*.
We moreover verify a polynomial-time coinductive fixed-point algorithm computing the coupled simulation preorder.
Through reduction proofs, we establish that deciding coupled similarity is at least as complex as computing weak similarity;
and that contrasimilarity checking is at least as hard as trace inclusion checking.
