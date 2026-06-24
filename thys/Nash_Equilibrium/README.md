# Nash Equilibria

This AFP-style Isabelle entry formalizes Nash equilibria for finite
strategic-form games.

It includes:

- finite normal-form games with player-indexed strategy sets;
- profiles, unilateral deviations, best responses, dominant strategies, and
  pure Nash equilibria;
- existence of pure Nash equilibria in finite ordinal potential games;
- existence from dominant-strategy profiles;
- matching pennies as a finite game with no pure Nash equilibrium;
- mixed-strategy profiles for finite games;
- support lemmas and Dirac embeddings connecting pure and mixed equilibria;
- existence of mixed Nash equilibria via Brouwer's fixed point theorem;
- formalized examples: Prisoner's Dilemma, a coordination game, matching
  pennies with its uniform mixed equilibrium, and rock-paper-scissors with its
  uniform mixed equilibrium.

Scope note: the pure-game locale supports player-indexed finite strategy sets.
The mixed-game locale uses finite HOL types for players and strategies, so all
players share the same finite pure-strategy type. This keeps mixed profiles as
Cartesian real vectors and makes the Brouwer proof fit HOL-Analysis directly.

Build with the bundled Isabelle installation from the monorepo root:

```powershell
& 'Q:\src\isabelle-borel-determinacy\toolchain\Isabelle2025-2\contrib\cygwin\bin\bash.exe' -lc 'cd /cygdrive/q/src/isabelle-afp-monorepo/projects/nash-equilibrium-isabelle && /cygdrive/q/src/isabelle-borel-determinacy/toolchain/Isabelle2025-2/bin/isabelle build -D . Nash_Equilibrium'
```
