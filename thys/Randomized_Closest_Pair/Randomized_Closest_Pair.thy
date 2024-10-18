section \<open>Introduction\<close>

text \<open>This entry formalizes Rabin's randomized closest points algorithm~\cite{rabin1976}, with
expected linear run-time.

Given a sequence of points in euclidean space, the algorithm finds the pair of points with the
smallest distance between them.

Remarkable is that the best known deterministic algorithm for this problem has running time
$\mathcal O(n \log n)$ for $n$ points~\cite[Section 1]{banyassady2007simple}. Some of them have been
formalized in Isabelle by Rau and Nipkow~\cite{Closest_Pair_Points-AFP, rau2020}.

The algorithm starts by choosing a grid-distance $d$, and storing the points in a square-grid
whose cells have that side-length.

Then it traverses the points, computing the distance of each with the points in the same (or
neighboring) cells in the square grid. (Two cells are considered neighboring, if they share an edge
or a vertex.)

The fundamental dilemma of the algorithm is the correct choice of $d$. If it is too small, then
it could happen that the two closest points of the sequence are not in neighboring cells. This means
$d$ must be chosen larger or equal to the closest-point distance of the sequence.
On the other hand, if $d$ is chosen too large, it may cause too many points ending up in the same
cell, which increases the running time.

The original algorithm by Rabin, chooses $d$ by sampling $n^{2/3}$ points and using the minimum
distance of those points. This can be computed using recursion (or a sub-quadratic deterministic
algorithm.)

An improvement to the algorithm, has been observed in a blog-post by Richard
Lipton~\cite{lipton2009}. Instead of obtaining a sub-sample of the points in the first step to
chose $d$, he observes that it is possible to sample $n$ independent point pairs and computing the
minimum distance of the pairs. The refined algorithm is considerably simpler, avoiding the need for
recursion. Similarly, the running time proof is simpler. (This entry formalizes this later version.)

In either case, the algorithm always returns the correct result with expected linear running time.

Note that, as far as I can tell, the proof of this new version has not been published. As such
this entry contains an informal proof for the results in each section.

Something that should be noted is that we assume a hypothetical data structure for the square-grid,
i.e., a mapping from a pair of integers identifying the cell to the points located in the cell,
that can be initialized in time $\mathcal O(n)$ and access time proportional to the count of points
in the cell (or $\mathcal O(1)$ if the cell is empty.) A naive implementation of such a data
structure would however have unbounded intialization time, if some points are really far apart.

The above was a discussion point that was raised by Fortune and Hopcroft~\cite{fortune1979}.
Later Dietzfelbinger~\cite{dietzfelbinger1997} resolved the issue by providing a concrete
implementation of the data structure using a hash table, with a hash function chosen randomly from
a pair-wise independent family, to guarantee the presumed costs of the hypothetical data structure
in expectation. However, for the sake of simplicity and consistency with Rabin's paper, we omit this
implementation detail, and pretend the hypothetical data structure exists.

Note also that, even with the hash table, it would not be possible to implement the algorithm in
linear time in Isabelle directly as it requires random-access arrays.

The following introduces a few primitive algorithms for the time monad, which will be followed
by the construction of the probabilistic time monad, which is necessary for the verification of
the expected running time. After which the algorithm will be formalized. Its properties will be
verified in the following sections.

\paragraph{Related Work:} Closely related is a recursive meshing based approach developed by Khuller
and  Matias~\cite{khuller1995} in 1995. Banyassady and Mulzer have given a new analysis of the
expected running time~\cite{banyassady2007simple} of Rabin's algorithm in 2007. However, this work
follows Rabin's original paper.\<close>

theory Randomized_Closest_Pair
  imports
    "HOL-Probability.Probability_Mass_Function"
    Root_Balanced_Tree.Time_Monad
    Karatsuba.Main_TM
    Closest_Pair_Points.Common
begin

hide_const (open) Giry_Monad.return

subsection \<open>Preliminary Algorithms in the Time Monad\<close>

text \<open>Time Monad version of @{term "min_list"}.\<close>

fun min_list_tm :: "'a::ord list \<Rightarrow> 'a tm" where
  "min_list_tm (x # y # zs) =1
    do {
      r \<leftarrow> min_list_tm (y#zs);
      Time_Monad.return (min x r)
    }" |
    "min_list_tm (x#[]) =1 Time_Monad.return x" |
    "min_list_tm [] =1 undefined"

lemma val_min_list: "xs \<noteq> [] \<Longrightarrow> val (min_list_tm xs) = min_list xs"
  by (induction xs rule:induct_list012) auto

lemma time_min_list: "xs \<noteq> [] \<Longrightarrow> time (min_list_tm xs) = length xs"
  by (induction xs rule:induct_list012) (simp_all)

text \<open>Time Monad version of @{term "remove1"}.\<close>

fun remove1_tm :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list tm"
  where
    "remove1_tm x (y#ys) =1 (
      if x = y then
        return ys
      else
        remove1_tm x ys \<bind> (\<lambda>r. return (y#r))
    )" |
    "remove1_tm x [] =1 return []"

lemma val_remove1: "val (remove1_tm x ys) = remove1 x ys"
  by (induction ys) simp+

lemma time_remove1: "time (remove1_tm x ys) \<le> 1 + length ys"
  by (induction ys) (simp_all)

text \<open>The following is a substitute for accounting for operations, where it was not possible to do
directly. One reason for this is that we abstract away the data structure of the grid (an infinite
2D-table), which properly implemented, would required the use of a hash table and $2$-independent
hash functions. A second reason is that we need to transfer the resource usage in the bind operation
of the probabilistic time monad (See below in the definition @{term "bind_tpmf"}).\<close>

fun custom_tick :: "nat \<Rightarrow> unit tm"
  where
    "custom_tick (Suc n) =1 custom_tick n" |
    "custom_tick 0 = return ()"

lemma time_custom_tick: "time (custom_tick n) = n" by (induction n) auto

subsection \<open>Probabilistic Time Monad\<close>

text \<open>The following defines the probabilistic time monad using the type @{typ "'a tm pmf"},
i.e., the algorithm returns a probability space of pairs of values and time-consumptions.

Note that the alternative type @{typ "'a pmf tm"}, i.e., a constant time consumption with a
value-distribution does not work since the running time may depend on random choices.\<close>

type_synonym 'a tpmf = "'a tm pmf"

definition bind_tpmf :: "'a tpmf \<Rightarrow> ('a \<Rightarrow> 'b tpmf) \<Rightarrow> 'b tpmf"
  where "bind_tpmf m f =
    do {
      x \<leftarrow> m;
      r \<leftarrow> f (val x);
      return_pmf (custom_tick (time x) \<bind> (\<lambda>_.  r))
    }"

definition return_tpmf :: "'a \<Rightarrow> 'a tpmf"
  where "return_tpmf x = return_pmf (return x)"

text \<open>The following allows the lifting of a deterministic algorithm in the time monad into the
probabilistic time monad.\<close>

definition lift_tm :: "'a tm \<Rightarrow> 'a tpmf"
  where "lift_tm x = return_pmf x"

text \<open>The following allows the lifting of a randomized algorithm into the probabilisitc time monad.
Note this should only be done, for primitive cases, as it requires accounting of the time usage.\<close>

definition lift_pmf :: "nat \<Rightarrow> 'a pmf \<Rightarrow> 'a tpmf"
  where "lift_pmf k m = map_pmf (\<lambda>x. custom_tick k \<bind> (\<lambda>_. return x)) m"

adhoc_overloading Monad_Syntax.bind bind_tpmf

lemma val_bind_tpmf:
  "map_pmf val (bind_tpmf m f) = map_pmf val m \<bind> (\<lambda>x. map_pmf val (f x))"
  (is "?L = ?R")
proof -
  have "map_pmf val (bind_tpmf m f) = m \<bind> (\<lambda>x. f (val x) \<bind> (\<lambda>x. return_pmf (val x)))"
    unfolding bind_tpmf_def map_bind_pmf by simp
  also have "... = ?R" unfolding bind_map_pmf by (simp add: map_pmf_def)
  finally show ?thesis by simp
qed

lemma val_return_tpmf:
  "map_pmf val (return_tpmf x) = return_pmf x"
  unfolding return_tpmf_def by simp

lemma val_lift_tpmf: "map_pmf val (lift_pmf k x) = x"
  unfolding lift_pmf_def val_bind_tpmf map_pmf_comp by simp

lemma val_lift_tm:
  "map_pmf val (lift_tm x) = return_pmf (val x)"
  unfolding lift_tm_def by simp

lemmas val_tpmf_simps = val_bind_tpmf val_lift_tpmf val_return_tpmf val_lift_tm

lemma time_return_tpmf: "map_pmf time (return_tpmf x) = return_pmf 0"
  unfolding return_tpmf_def by simp

lemma time_lift_pmf: "map_pmf time (lift_pmf x p) = return_pmf x"
  unfolding lift_pmf_def map_pmf_comp by (simp add: time_custom_tick)

lemma time_bind_tpmf: "map_pmf time (bind_tpmf m f) =
  do {
    x \<leftarrow> m;
    y \<leftarrow> f (val x);
    return_pmf (time x + time y)
  }"
  unfolding bind_tpmf_def map_bind_pmf by (simp add:time_custom_tick)

lemma bind_return_tm: "bind_tm (Time_Monad.return x) f = f x"
  by (simp add:tm_simps  tm.case_eq_if)

lemma bind_return_tpmf: "bind_tpmf (return_tpmf x) f = (f x)"
  unfolding bind_tpmf_def return_tpmf_def
  by (simp add:bind_return_pmf bind_return_tm bind_return_pmf')

text \<open>Version of @{term "replicate_pmf"} for the probabilistic time monad.\<close>

fun replicate_tpmf :: "nat \<Rightarrow> 'a tpmf \<Rightarrow> 'a list tpmf"
  where
    "replicate_tpmf 0 p = return_tpmf []" |
    "replicate_tpmf (Suc n) p =
      do {
        x \<leftarrow> p;
        y \<leftarrow> replicate_tpmf n p;
        return_tpmf (x#y)
      }"


lemma time_replicate_tpmf:
  "map_pmf time (replicate_tpmf n p) = map_pmf sum_list (replicate_pmf n (map_pmf time p))"
proof (induction n)
  case 0 thus ?case by (simp add:time_return_tpmf)
next
  case (Suc n)
  have "map_pmf time (replicate_tpmf (Suc n) p) =
    p \<bind> (\<lambda>x. replicate_tpmf n p \<bind> (\<lambda>y. return_pmf (time x + time y)))"
    by (simp add: time_bind_tpmf return_tpmf_def)
     (simp add: bind_tpmf_def bind_assoc_pmf bind_return_pmf time_custom_tick)
  also have "\<dots> = map_pmf time p \<bind>
    (\<lambda>x. map_pmf time (replicate_tpmf n p) \<bind> (\<lambda>y. return_pmf (x + y)))"
    unfolding map_pmf_def by (simp add:bind_assoc_pmf bind_return_pmf)
  also have "\<dots> = map_pmf time p \<bind> (\<lambda>x. replicate_pmf n (map_pmf time p) \<bind>
    (\<lambda>y. return_pmf (x + sum_list y)))"
    by (subst Suc) (metis (no_types, lifting) bind_map_pmf bind_pmf_cong)
  also have "\<dots> = map_pmf sum_list (replicate_pmf (Suc n) (map_pmf time p))"
    by (simp add:map_bind_pmf)
  finally show ?case by simp
qed

lemma val_replicate_tpmf:
  "map_pmf val (replicate_tpmf n x) = replicate_pmf n (map_pmf val x)"
  by (induction n) (simp_all add:val_tpmf_simps)

lemma set_val_replicate_tpmf:
  assumes "xs \<in> set_pmf (replicate_tpmf n p)"
  shows "length (val xs) = n" "set (val xs) \<subseteq> val ` set_pmf p"
proof -
  have "val xs \<in> set_pmf (map_pmf val (replicate_tpmf n p))" using assms by simp
  thus "length (val xs) = n"  "set (val xs) \<subseteq> val ` set_pmf p"
    unfolding val_replicate_tpmf set_replicate_pmf by auto
qed

lemma replicate_return_pmf[simp]: "replicate_pmf n (return_pmf x) = return_pmf (replicate n x)"
  by (induction n) (simp_all add:bind_return_pmf)

subsection \<open>Randomized Closest Points Algorithm\<close>

text \<open>Using the above we can express the randomized closests points algorithm in the
probabilistic time monad.\<close>

type_synonym point = "real^2"

record grid =
  g_dist :: real
  g_lookup :: "int * int \<Rightarrow> point list tm"

definition to_grid :: "real \<Rightarrow> point \<Rightarrow> int * int"
  where "to_grid d x = (\<lfloor>x $ 1/d\<rfloor>,\<lfloor>x $ 2/d\<rfloor>)"

text \<open>This represents the grid data-structure mentioned before. We assume the build time is linear
to the number of points stored and the access time is at least $\mathcal O(1)$ and proportional
to the number of points in the cell. (In practice this would be implemented using hash functions.)\<close>

definition build_grid :: "point list \<Rightarrow> real \<Rightarrow> grid tm" where
  "build_grid xs d =
  do {
    _ \<leftarrow> custom_tick (length xs);
    return \<lparr>
      g_dist = d,
      g_lookup = (\<lambda>q. map_tm return (filter (\<lambda>x. to_grid d x = q) xs))
    \<rparr>
  }"

definition sample_distance :: "point list \<Rightarrow> real tpmf" where
  "sample_distance ps = do {
    i \<leftarrow> lift_pmf 1 (pmf_of_set {i. fst i < snd i \<and> snd i < length ps});
    return_tpmf (dist (ps ! (fst i)) (ps ! (snd i)))
  }"

lemma val_sample_distance:
  "map_pmf val (sample_distance ps) = map_pmf (\<lambda>i. dist (ps ! (fst i)) (ps ! (snd i)))
  (pmf_of_set  {i. fst i < snd i \<and> snd i < length ps})"
  unfolding sample_distance_def by (simp add:val_tpmf_simps) (simp add:map_pmf_def)

definition first_phase :: "point list \<Rightarrow> real tpmf" where
  "first_phase ps = do {
    ds \<leftarrow> replicate_tpmf (length ps) (sample_distance ps);
    lift_tm (min_list_tm ds)
  }"

definition lookup_neighborhood :: "grid \<Rightarrow> point \<Rightarrow> point list tm"
  where "lookup_neighborhood grid p =
    do {
      d \<leftarrow> tick (g_dist grid);
      q \<leftarrow> tick (to_grid d p);
      cs \<leftarrow> map_tm (\<lambda>x. tick (x + q)) [(0,0),(0,1),(1,-1),(1,0),(1,1)];
      map_tm (g_lookup grid) cs \<bind> concat_tm \<bind> remove1_tm p
    }"

text \<open>This function collects all points in the cell of the given point and those from the
neighboring cells. Here it is relevant to note that only half of the neighboring cells are
taken. This is because of symmetry, i.e., if point $p$ is north-east of point $q$, then $q$
is south-west of point $q$. Since all points are being traversed it is enough to restrict
the neighbor set.\<close>

definition calc_dists_neighborhood :: "grid \<Rightarrow> point \<Rightarrow> real list tm"
  where "calc_dists_neighborhood grid p =
    do {
      ns \<leftarrow> lookup_neighborhood grid p;
      map_tm (tick \<circ> dist p) ns
    }"

definition second_phase :: "real \<Rightarrow> point list \<Rightarrow> real tm" where
  "second_phase d ps = do {
    grid \<leftarrow> build_grid ps d;
    ns \<leftarrow> map_tm (calc_dists_neighborhood grid) ps;
    concat_tm ns \<bind> min_list_tm
  }"

definition closest_pair :: "point list \<Rightarrow> real tpmf" where
  "closest_pair ps = do {
    d \<leftarrow> first_phase ps;
    if d = 0 then
      lift_tm (tick 0)
    else
      lift_tm (second_phase d ps)
  }"

end