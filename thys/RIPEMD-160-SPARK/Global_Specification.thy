section "Global Specifications"
theory Global_Specification
imports RMD

begin


text {* SPARK has only one integer-type, therefore type-conversions
  are needed in order to specify the proof-functions in Isabelle. *}


subsection {* Specification of Bit-Operations *}

text {* The proof-functions for SPARK's bit-opertations are specified
with HOL-Word *}

abbreviation bit__and' :: "int => int => int" where
  "bit__and' m n == uint ((word_of_int m::word32) AND word_of_int n)"

abbreviation bit__or' :: "int => int => int" where
  "bit__or' m n == uint ((word_of_int m::word32) OR word_of_int n)"

abbreviation bit__xor' :: "int => int => int" where
  "bit__xor' m n == uint ((word_of_int m::word32) XOR word_of_int n)"

abbreviation rotate_left' :: "int => int => int" where
  "rotate_left' i w == uint (word_rotl (nat i) (word_of_int w::word32))"

text{* This is how SPARK treats the bitwise not *}

lemma bit_not_spark_def[simp]:
  "(word_of_int (4294967295 - x)::word32) = NOT (word_of_int x)"
proof -
  have "word_of_int x + (word_of_int (4294967295 - x)::word32) =
          word_of_int x + NOT (word_of_int x)"
    by (simp only: bwsimps bin_add_not Min_def) simp
  thus ?thesis by (simp only: add_left_imp_eq)
qed

subsection{* Conversions for proof functions *}

text{* Here, the proof-functions declared in the SPARK-Annotations are
  mapped to the corresponding parts of the Isabelle-Specification. *}

abbreviation k_l' :: "int => int" where
  "k_l' j == uint (K (nat j))"
abbreviation k_r' :: "int => int" where
  "k_r' j == uint (K' (nat j))"
abbreviation r_l' :: "int => int" where
  "r_l' j == int (r (nat j))"
abbreviation r_r' :: "int => int" where
  "r_r' j == int (r' (nat j))"
abbreviation s_l' :: "int => int" where
  "s_l' j == int (s (nat j))"
abbreviation s_r' :: "int => int" where
  "s_r' j == int (s' (nat j))"
abbreviation f' :: "int => int => int => int => int" where
  "f' j x y z ==
    uint (f (nat j) (word_of_int x::word32) (word_of_int y) (word_of_int z))"


end
