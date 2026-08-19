theory BMSSP_Executable_Headline
  imports BMSSP_Executable_Refinement
begin

section \<open>Executable Headline\<close>

text \<open>
  This theory states the headline correctness theorem of the entire
  development.  It is the entry point for a reader who wants one statement
  that summarises what is proved, and it is the theorem that should be
  consulted before any other.  The body of the proof is a short forward
  reference to the verified executable contract.

  The headline applies to the executable entry point
  @{const bmssp_distances}, which takes a finite directed graph of natural
  vertices with natural-valued edge weights and a source vertex, and returns
  a finite association list mapping each reachable vertex to its
  shortest-path distance from the source.  The graph representation
  @{typ nat_graph}, the well-formedness predicate
  @{const nat_graph_well_formed}, the vertex set @{const nat_graph_vertices},
  the reachability relation @{const nat_graph_reachable}, and the shortest
  distance function @{const nat_graph_dist} are all defined earlier in the
  session and used unchanged here.

  The theorem below is intentionally a single complete statement.  It exposes
  soundness, completeness, and uniqueness of output keys together, so readers
  do not have to reconstruct the exact map property from several smaller
  auxiliary facts.
\<close>

theorem bmssp_correct_strong:
  assumes well_formed: "nat_graph_well_formed G"
    and src_in: "src \<in> nat_graph_vertices G"
  shows
    "distinct (map fst (bmssp_distances G src)) \<and>
     set (map fst (bmssp_distances G src)) =
       {v \<in> nat_graph_vertices G. nat_graph_reachable G src v} \<and>
     (\<forall>(v, d) \<in> set (bmssp_distances G src).
        real d = nat_graph_dist G src v)"
proof -
  interpret inst: nat_graph_instance G src
    by standard (rule well_formed, rule src_in)
  have distinct_keys:
    "distinct (map fst (bmssp_distances G src))"
    by (rule BMSSP_Executable_Refinement.bmssp_distances_distinct_keys)
  have output_subset:
    "set (map fst (bmssp_distances G src)) \<subseteq>
      {v \<in> nat_graph_vertices G. nat_graph_reachable G src v}"
  proof
    fix v
    assume v_key: "v \<in> set (map fst (bmssp_distances G src))"
    then obtain d where mem: "(v, d) \<in> set (bmssp_distances G src)"
      by force
    have v_vertices: "v \<in> nat_graph_vertices G"
      using inst.bmssp_distances_keys_subset_carrier v_key by blast
    have reachable: "nat_graph_reachable G src v"
      by (rule inst.bmssp_distances_output_reachable[OF mem])
    show "v \<in> {v \<in> nat_graph_vertices G. nat_graph_reachable G src v}"
      using v_vertices reachable by simp
  qed
  have reachable_subset:
    "{v \<in> nat_graph_vertices G. nat_graph_reachable G src v} \<subseteq>
      set (map fst (bmssp_distances G src))"
  proof
    fix v
    assume "v \<in> {v \<in> nat_graph_vertices G. nat_graph_reachable G src v}"
    then have v_vertices: "v \<in> nat_graph_vertices G"
      and reachable: "nat_graph_reachable G src v"
      by simp_all
    obtain d where "(v, d) \<in> set (bmssp_distances G src)"
      using BMSSP_Executable_Refinement.bmssp_correct_executable(2)
        [OF well_formed src_in] v_vertices reachable by blast
    then show "v \<in> set (map fst (bmssp_distances G src))"
      by force
  qed
  have exact_distances:
    "\<forall>(v, d) \<in> set (bmssp_distances G src).
       real d = nat_graph_dist G src v"
    by (rule BMSSP_Executable_Refinement.bmssp_correct_executable(1)
        [OF well_formed src_in])
  have key_set:
    "set (map fst (bmssp_distances G src)) =
      {v \<in> nat_graph_vertices G. nat_graph_reachable G src v}"
    using output_subset reachable_subset by blast
  show ?thesis
    using distinct_keys key_set exact_distances by blast
qed

text \<open>
  The proof combines the underlying executable theorem
  @{thm BMSSP_Executable_Refinement.bmssp_correct_executable} with the
  distinct-key and output-reachability facts from the executable refinement
  layer.  The two clauses of @{thm BMSSP_Executable_Refinement.bmssp_correct_executable}
  give exact distances for every returned pair and completeness for every
  reachable vertex; the local key-set argument above adds the converse
  inclusion and the distinctness statement.

  The proof is deliberately structured rather than written as a one-line
  automation script.  The intention is to make the proof obligation visible
  and to expose how the headline is derived from the verified executable
  contract.  The automated steps are confined to small set and tuple
  manipulations after the named refinement facts have been supplied.  Tracing
  the proof reveals exactly which named theorem proves what.

  In short, the entire development reduces to:
  \begin{itemize}
  \item @{const bmssp_distances} computes a finite list of pairs.
  \item For every well-formed graph and every source vertex of that graph,
        every returned pair gives the exact shortest-path distance from the
        source.
  \item For every well-formed graph and every source vertex of that graph,
        every reachable vertex appears in the output, and no unreachable
        vertex appears.
  \end{itemize}
  The remaining theories prove these facts.  This file states them.
\<close>

end
