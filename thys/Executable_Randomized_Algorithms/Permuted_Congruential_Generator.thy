section \<open>A Pseudo-random Number Generator\label{sec:permuted_congruential_generator}\<close>

text \<open>In this section we introduce a PRG, that can be used to generate random bits. It is an
implementation of O'Neil's Permuted congruential generator~\cite{oneill2014}
(specifically PCG-XSH-RR). In empirical tests it ranks high~\cite{bhattacharjee2018, singh2020}
while having a low implementation complexity.

This is for easy testing purposes only, the generated code can be run with any source of random
bits.\<close>

theory Permuted_Congruential_Generator
  imports
    "HOL-Library.Word"
    "Coin_Space"
begin

text \<open>The following are default constants from the reference implementation~\cite{pcgbasic}.\<close>

definition pcg_mult :: "64 word"
  where "pcg_mult = 6364136223846793005"
definition pcg_increment :: "64 word"
  where "pcg_increment = 1442695040888963407"

fun pcg_rotr :: "32 word \<Rightarrow> nat \<Rightarrow> 32 word"
  where "pcg_rotr x r = Bit_Operations.or (drop_bit r x) (push_bit (32-r) x)"

fun pcg_step :: "64 word \<Rightarrow> 64 word"
  where "pcg_step state = state * pcg_mult + pcg_increment"

text \<open>Based on \cite[Section~6.3.1]{oneill2014}:\<close>

fun pcg_get :: "64 word \<Rightarrow> 32 word"
  where "pcg_get state =
    (let count = unsigned (drop_bit 59 state);
         x     = xor (drop_bit 18 state) state
      in pcg_rotr (ucast (drop_bit 27 x)) count)"

fun pcg_init :: "64 word \<Rightarrow> 64 word"
  where "pcg_init seed = pcg_step (seed + pcg_increment)"

definition to_bits :: "32 word \<Rightarrow> bool list"
  where "to_bits x = map (\<lambda>k. bit x k) [0..<32]"

definition random_coins
  where "random_coins seed = build_coin_gen (to_bits \<circ> pcg_get) pcg_step (pcg_init seed)"

end