(* Title: Stream_Fusion_Examples
  Author: Andreas Lochbihler, ETH Zurich *)

section {* Examples and test cases for stream fusion *}

theory Stream_Fusion_Examples imports Stream_Fusion_LList begin

lemma fixes rhs z
  defines "rhs \<equiv> nth_cons (flatten (\<lambda>s'. s') (upto_prod 17) (upto_prod z)) (2, None) 8"
  shows "nth (List.maps (\<lambda>x. upto x 17) (upto 2 z)) 8 = rhs"
using [[simproc add: stream_fusion, stream_fusion_trace]]
apply(simp del: id_apply) -- {* fuses *}
by(unfold rhs_def) rule

lemma fixes rhs z
  defines "rhs \<equiv> nth_cons (flatten (\<lambda>s. (s, 1)) (fix_gen (\<lambda>x. upto_prod (id x))) (upto_prod z)) (2, None) 8"
  shows "nth (List.maps (\<lambda>x. upto 1 (id x)) (upto 2 z)) 8 = rhs"
using [[simproc add: stream_fusion, stream_fusion_trace]]
apply(simp del: id_apply) -- {* fuses *}
by(unfold rhs_def) rule

lemma fixes rhs n
  defines "rhs \<equiv> List.maps (\<lambda>x. [Suc 0..<listsum_cons (replicate_prod x) x]) [2..<n]"
  shows "(concat (map (\<lambda>x. [1..<listsum (replicate x x)]) [2..<n])) = rhs"
using [[simproc add: stream_fusion, stream_fusion_trace]]
apply(simp add: concat_map_maps) -- {* fuses partially *}
by(unfold rhs_def) rule

subsection {* Micro-benchmarks from Farmer et al. \cite{FarmerHoenerGill2014PEPM} *}

definition test_enum :: "nat \<Rightarrow> nat" -- {* @{const id} required to avoid eta contraction *}
where "test_enum n = foldl (op +) 0 (List.maps (\<lambda>x. upt 1 (id x)) (upt 1 n))"

definition test_nested :: "nat \<Rightarrow> nat"
where "test_nested n = foldl (op +) 0 (List.maps (\<lambda>x. List.maps (\<lambda>y. upt y x) (upt 1 x)) (upt 1 n))"

definition test_merge :: "integer \<Rightarrow> nat"
where "test_merge n = foldl (op +) 0 (List.maps (\<lambda>x. if 2 dvd x then upt 1 x else upt 2 x) (upt 1 (nat_of_integer n)))"

text {*
  This rule performs the merge operation from \cite[\S 5.2]{FarmerHoenerGill2014PEPM} for @{text "if"}.
  In general, we would also need it for all case operators.
*}
lemma unstream_if [stream_fusion]:
  "unstream (if b then g else g') (if b then s else s') =
   (if b then unstream g s else unstream g' s')"
by simp

lemma if_same [code_unfold]: "(if b then x else x) = x"
by simp

code_thms test_enum
code_thms test_nested
code_thms test_merge

subsection {* Test stream fusion in the code generator *}

definition fuse_test :: integer
where "fuse_test = 
  integer_of_int (lhd (lfilter (\<lambda>x. x < 1) (lappend (lmap (\<lambda>x. x + 1) (llist_of (map (\<lambda>x. if x = 0 then undefined else x) [-3..5]))) (repeat 3))))"

ML_val {* val ~2 = @{code fuse_test} *} -- {*
  If this test fails with exception Fail, then the stream fusion simproc failed. This test exploits
  that stream fusion introduces laziness. *}

end
