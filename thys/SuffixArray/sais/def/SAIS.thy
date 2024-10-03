theory SAIS
  imports Induce Get_Types
begin

section "SAIS"

function sais_r0 ::
  "nat list \<Rightarrow>
   nat list"
  where
"sais_r0 [] = []" |
"sais_r0 [x] = [0]" |
"sais_r0 (a # b # xs) =
  (let
      T = a # b # xs;

      \<comment>\<open> Compute the suffix types \<close>
      ST = abs_get_suffix_types T;

      \<comment>\<open> Extract the LMS types \<close>
      LMS0 = extract_lms ST [0..<length T];

      \<comment>\<open> Induce the prefix ordering based on LMS \<close>
      SA = sa_induce id T ST LMS0;

      \<comment>\<open> Extract the LMS types \<close>
      LMS1 = extract_lms ST SA;

      \<comment>\<open> Create a new alphabet \<close>
      names = rename_mapping T ST LMS1;

      \<comment>\<open> Make a reduced string (2 lines) \<close>
      T' = rename_string LMS0 names;

      \<comment>\<open> Obtain the correct ordering of LMS-types \<close>
      LMS2 = (if distinct T' then LMS1 else order_lms LMS0 (sais_r0 T'))

   \<comment>\<open> Induce the suffix ordering based of LMS \<close>
   in sa_induce id T ST LMS2)"
  by pat_completeness blast+

function sais_r1 ::
  "nat list \<Rightarrow>
   nat list"              
  where
"sais_r1 [] = []" |
"sais_r1 [x] = [0]" |
"sais_r1 (a # b # xs) =
  (let
      T = a # b # xs;

      \<comment>\<open> Compute the suffix types \<close>
      ST = get_suffix_types T;

      \<comment>\<open> Extract the LMS types \<close>
      LMS0 = extract_lms ST [0..<length T];

      \<comment>\<open> Induce the prefix ordering based on LMS \<close>
      SA = sa_induce id T ST LMS0;

      \<comment>\<open> Extract the LMS types \<close>
      LMS1 = extract_lms ST SA;

      \<comment>\<open> Create a new alphabet \<close>
      names = rename_mapping T ST LMS1;

      \<comment>\<open> Make a reduced string \<close>
      T' = rename_string LMS0 names;

      \<comment>\<open> Obtain the correct ordering of LMS-types \<close>
      LMS2 = (if distinct T' then LMS1 else order_lms LMS0 (sais_r1 T'))

   \<comment>\<open> Induce the suffix ordering based of LMS \<close>
   in sa_induce id T ST LMS2)"
  by pat_completeness blast+

abbreviation "sais \<equiv> sais_r1"

end