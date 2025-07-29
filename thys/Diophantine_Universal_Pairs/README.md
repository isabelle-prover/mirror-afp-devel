# Formalization of Complexity Bounds on Diophantine Equations

Isabelle version: Isabelle2025

**Authors:** Jonas Bayer, Marco David, Timothé Ringeard, Xavier Pigé, Anna Danilkin, Mathis Bouverot-Dupuis, Paul Wang, Quentin Vermande, Theo André, Loïc Chevalier, Charlotte Dorneich, Eva Brenner, Chris Ye, Kevin Lee, Annie Yao

## Setup 
1. The Isabelle code depends on the Isabelle/AFP. Follow the instructions on the AFP website https://www.isa-afp.org/help/ to install it. 
2. Run `isabelle jedit -d . -R Universal_Pairs` in a terminal (in the project directory) to open the formalization. If you are using Windows you need to use the Isabelle cygwin terminal. This makes sure that dependencies are prechecked which significantly improves the editing experience. You might have to wait a while for this process to complete. 

## Structure of the formalization
The theorem numbering in the Isabelle code corresponds to the mathematical manuscript.
The folders Coding and Coding\_Theorem were formerly named Theorem\_I.
The folder Bridge\_Theorem was formerly named Theorem\_II and depends on the theory developed in Lucas\_Sequences.
The folder Nine_Unknowns\_N\_Z was formerly named Theorem\_III.