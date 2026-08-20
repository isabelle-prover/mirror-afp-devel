theory Erdos_Ginzburg_Ziv_Outline
  imports
    Erdos_Ginzburg_Ziv
begin

section \<open>Overview\<close>

text \<open>
  This entry formalizes the Erd\H{o}s-Ginzburg-Ziv theorem for integer multisets.
  The development is layered as follows: the basics theory develops modular
  subset-sum infrastructure, the prime theory proves the prime-modulus case,
  and the final theory derives the full theorem for arbitrary positive moduli
  by strong induction.
\<close>

section \<open>Main results\<close>

text \<open>
  The main exported facts are @{text prime_egz}, for prime moduli, and
  @{text erdos_ginzburg_ziv}, for the arbitrary-modulus monotone form. The
  latter states that every integer multiset of size at least @{text "2 * n - 1"}
  has an @{term n}-element submultiset whose sum is divisible by @{term n}.
\<close>

section \<open>Proof architecture\<close>

text \<open>
  In the prime case, either some residue already occurs @{term p} times or the
  residues can be sorted and paired so that the lower-to-upper gaps are all
  nonzero modulo @{term p}. Subset sums of those gaps then cover the entire
  residue system and yield the required correction term.

  For composite @{term n}, write @{text "n = m * p"} with @{term p} prime.
  Repeated applications of the prime theorem produce @{text "2 * m - 1"}
  disjoint @{term p}-blocks whose sums are divisible by @{term p}; applying the
  induction hypothesis to the corresponding quotients selects blocks whose union
  gives the desired @{term n}-element zero-sum submultiset.
\<close>

end
