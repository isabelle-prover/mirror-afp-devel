(*
  File:    CRT_Product_Tree_Benchmark.thy
  Author:  Manuel Eberl, University of Innsbruck
*)
subsection \<open>Examples and Benchmarks\<close>
theory CRT_Product_Tree_Benchmark
  imports CRT_Product_Tree "HOL-Library.Code_Target_Numeral"
begin

text \<open>
  As a simple example, consider the following system of congruences:
  \[
     \begin{aligned}
      x&\equiv 0{\pmod {3}}\\
      x&\equiv 3{\pmod {4}}\\
      x&\equiv 4{\pmod {5}}
     \end{aligned}
  \]
  We use our algorithm \<^const>\<open>crt_prodtree\<close> to find that this is equivalent to the single
  congruence $x\equiv 39{\pmod {60}}$:
\<close>

value "crt_prodtree [(0, 3), (3, 4), (4, 5 :: int)]"


text \<open>
  Next, we compare the product tree implementation to a more na\"ive divice-and-conquer
  implementation that simply computes the CRT by computing the binary CRT of adjacent pairs in a 
  list, thereby halving the list, and doing this iteratively until there is only one pair left.
\<close>

fun slow_crt_aux :: "(int \<times> int) list \<Rightarrow> (int \<times> int) list" where
  "slow_crt_aux [] = []"
| "slow_crt_aux [x] = [x]"
| "slow_crt_aux ((x1, m1) # (x2, m2) # xs) =
     (case bezout_coefficients m1 m2 of
       (a1, a2) \<Rightarrow> ((x1 * a2) mod m1 * m2 + (x2 * a1) mod m2 * m1, m1 * m2)) # slow_crt_aux xs"

lemma length_slow_crt_aux [simp]: "length (slow_crt_aux xs) = (length xs + 1) div 2"
  by (induction xs rule: slow_crt_aux.induct) auto

function slow_crt :: "(int \<times> int) list \<Rightarrow> int \<times> int" where
  "slow_crt xs =
     (case xs of
        [] \<Rightarrow> (0, 0)
      | (x, m) # xs' \<Rightarrow> if xs' = [] then (x mod m, m) else slow_crt (slow_crt_aux xs))"
  by auto
termination by (relation "measure length") auto

definition mk_test_data :: "(integer \<times> integer) list \<Rightarrow> (int \<times> int) list" where
  "mk_test_data = map (map_prod int_of_integer int_of_integer)"
definition "test_crt_prodtree = map_prod integer_of_int integer_of_int o crt_prodtree"
definition "test_slow_crt = map_prod integer_of_int integer_of_int o slow_crt"


text \<open>
  We test the implementations on a list of $n$ pairs of the form $(i, p_i)$, where $p_i$ is the
  $i$-th prime number. The benchmark shows that, empirically, the product tree implementation takes
  time $\widetilde{O}(n)$, whereas the na\"ive implementation takes time $\widetilde{O}(n^2)$.

  This agrees with what one would expect from the theory: the na\"ive implementation performs
  $\frac{n}{2^i}$ Extended Euclidean algorithm (EEA) computations on $\Theta(2^i)$ bit numbers in
  the $i$-th iteration. The standard implementation of the EEA is quadratic, leading to quadratic
  effort overall. The product tree implementation only performs a constant number of
  multiplications and divisions (which are significantly faster than quadratic) at every node 
  of the tree, leading to linear behaviour.

  It should be noted that using an asymptotically faster EEA implementation would theoretically 
  fix this issue and make the na\"ive divide-and-conquer algorithm roughly as fast as the 
  product tree one, but these algorithms are very complicated and have large constant factor 
  overheads, making this impractical.
\<close>

ML \<open>
(*
  a simple Eratosthenes-style sieve; 
  result array contains smallest prime divisor for composites and 0 for primes, 0, and 1
*)
fun prime_sieve n =
  let
    val a = Array.array (n+1, 0)
    fun mark i k =
      if i > n then ()
      else let val _ = Array.update (a, i, k) in mark (i + k) k end
    fun go k =
      if k * k > n then ()
      else if Array.sub (a, k) <> 0 then go (k+1)
      else let val _ = mark (k * k) k in go (k+1) end
    val _ = go 2
  in
    a
  end

fun primes_upto n =
  let
    val a = prime_sieve n
    fun go i acc =
      if i > n then rev acc
      else go (i+1) (if Array.sub (a, i) = 0 then i :: acc else acc)
  in
    go 2 []
  end
\<close>

ML \<open>
local
  exception NOT_ENOUGH_PRIMES
  val max_prime = 500000
  val mk_test_data_aux = @{code mk_test_data}

  val (t_ps, ps) = Timing.timing primes_upto max_prime
  val _ = writeln ( "Sieving primes up to " ^ Int.toString max_prime
     ^ ": " ^ Time.message (#elapsed t_ps) ^ "\n")
  val n_ps = length ps

  fun mk_test_data n =
    if n > n_ps then
      raise NOT_ENOUGH_PRIMES
    else
      take n ps |> map_index I |> mk_test_data_aux

  val test_crt_prodtree = @{code test_crt_prodtree}
  val test_slow_crt = @{code test_slow_crt}
  fun test n =
    let
      val dat = mk_test_data n
      val _ = writeln ("Testing with " ^ Int.toString n ^ " primes.")
      val (t1, _) = Timing.timing test_crt_prodtree dat
      val _ = writeln ("crt_prodtree: " ^ Time.message (#elapsed t1))
      val (t2, _) = Timing.timing test_slow_crt dat
      val _ = writeln ("slow_crt: " ^ Time.message (#elapsed t2))
      val speedup = Time.toReal (#elapsed t2) / Time.toReal (#elapsed t1)
      val _ = writeln ("Speedup: " ^ Real.fmt (StringCvt.FIX (SOME 2)) speedup ^ "\n")
    in
      ()
    end
in
  val _ = map test [10000, 14142, 20000, 28284, 40000]
end
\<close>

end
