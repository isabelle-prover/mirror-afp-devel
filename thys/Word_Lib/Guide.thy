(*<*)
theory Guide
  imports Main Word_Lemmas Word_Lemmas_32 Word_Lemmas_64
begin

hide_const (open) Misc_set_bit.set_bit

(*>*)
section \<open>A short overview over bit operations and word types\<close>

subsection \<open>Basic theories and key ideas\<close>

text \<open>
  When formalizing bit operations, it is tempting to represent
  bit values as explicit lists over a binary type. This however
  is a bad idea, mainly due to the inherent ambiguities in
  representation concerning repeating leading bits.

  Hence this approach avoids such explicit lists altogether
  following an algebraic path:

    \<^item> Bit values are represented by numeric types: idealized
      unbounded bit values can be represented by type \<^typ>\<open>int\<close>,
      bounded bit values by quotient types over \<^typ>\<open>int\<close>, aka \<^typ>\<open>'a word\<close>.

    \<^item> (A special case are idealized unbounded bit values ending
      in @{term [source] 0} which can be represented by type \<^typ>\<open>nat\<close> but
      only support a restricted set of operations).

  The most fundamental ideas are developed in theory \<^theory>\<open>HOL.Parity\<close>
  (which is part of \<^theory>\<open>Main\<close>):

    \<^item> Multiplication by \<^term>\<open>2 :: int\<close> is a bit shift to the left and

    \<^item> Division by \<^term>\<open>2 :: int\<close> is a bit shift to the right.

    \<^item> Concerning bounded bit values, iterated shifts to the left
    may result in eliminating all bits by shifting them all
    beyond the boundary.  The property \<^prop>\<open>(2 :: int) ^ n \<noteq> 0\<close>
    represents that \<^term>\<open>n\<close> is \<^emph>\<open>not\<close> beyond that boundary.

    \<^item> The projection on a single bit is then @{thm [mode=iff] bit_iff_odd [where ?'a = int, no_vars]}.

    \<^item> This leads to the most fundamental properties of bit values:

      \<^item> Equality rule: @{thm [display, mode=iff] bit_eq_iff [where ?'a = int, no_vars]}

      \<^item> Induction rule: @{thm [display, mode=iff] bits_induct [where ?'a = int, no_vars]}

  On top of this, the following generic operations are provided
  after import of theory \<^theory>\<open>HOL-Library.Bit_Operations\<close>:

    \<^item> Singleton \<^term>\<open>n\<close>th bit: \<^term>\<open>(2 :: int) ^ n\<close>

    \<^item> Bit mask upto bit \<^term>\<open>n\<close>: @{thm mask_eq_exp_minus_1 [where ?'a = int, no_vars]}

    \<^item> Left shift: @{thm push_bit_eq_mult [where ?'a = int, no_vars]}

    \<^item> Right shift: @{thm drop_bit_eq_div [where ?'a = int, no_vars]}

    \<^item> Truncation: @{thm take_bit_eq_mod [where ?'a = int, no_vars]}

    \<^item> Negation: @{thm [mode=iff] bit_not_iff [where ?'a = int, no_vars]}

    \<^item> And: @{thm [mode=iff] bit_and_iff [where ?'a = int, no_vars]}

    \<^item> Or: @{thm [mode=iff] bit_or_iff [where ?'a = int, no_vars]}

    \<^item> Xor: @{thm [mode=iff] bit_xor_iff [where ?'a = int, no_vars]}

    \<^item> Set a single bit: @{thm set_bit_def [where ?'a = int, no_vars]}

    \<^item> Unset a single bit: @{thm unset_bit_def [where ?'a = int, no_vars]}

    \<^item> Flip a single bit: @{thm flip_bit_def [where ?'a = int, no_vars]}

    \<^item> Signed truncation, or modulus centered around \<^term>\<open>0::int\<close>:
        @{thm [display] signed_take_bit_def [where ?'a = int, no_vars]}

    \<^item> (Bounded) conversion from and to a list of bits:
        @{thm [display] horner_sum_bit_eq_take_bit [where ?'a = int, no_vars]}

  Proper word types are introduced in theory \<^theory>\<open>HOL-Word.Word\<close>, with
  the following specific operations:

    \<^item> Standard arithmetic:
        @{term \<open>(+) :: 'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>},
        @{term \<open>uminus :: 'a::len word \<Rightarrow> 'a word\<close>},
        @{term \<open>(-) :: 'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>},
        @{term \<open>(*) :: 'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>},
        @{term \<open>0 :: 'a::len word\<close>}, @{term \<open>1 :: 'a::len word\<close>}, numerals etc.

    \<^item> Standard bit operations: see above.

    \<^item> Conversion with unsigned interpretation of words:

        \<^item> @{term [source] \<open>unsigned :: 'a::len word \<Rightarrow> 'b::semiring_1\<close>}

        \<^item> Important special cases as abbreviations:

            \<^item> @{term [source] \<open>unat :: 'a::len word \<Rightarrow> nat\<close>}

            \<^item> @{term [source] \<open>uint :: 'a::len word \<Rightarrow> int\<close>}

            \<^item> @{term [source] \<open>ucast :: 'a::len word \<Rightarrow> 'b::len word\<close>}

    \<^item> Conversion with signed interpretation of words:

        \<^item> @{term [source] \<open>signed :: 'a::len word \<Rightarrow> 'b::ring_1\<close>}

        \<^item> Important special cases as abbreviations:

            \<^item> @{term [source] \<open>sint :: 'a::len word \<Rightarrow> int\<close>}

            \<^item> @{term [source] \<open>scast :: 'a::len word \<Rightarrow> 'b::len word\<close>}

    \<^item> Operations with unsigned interpretation of words:

        \<^item> @{thm [mode=iff] word_le_nat_alt [no_vars]}

        \<^item> @{thm [mode=iff] word_less_nat_alt [no_vars]}

        \<^item> @{thm unat_div_distrib [no_vars]}

        \<^item> @{thm unat_drop_bit_eq [no_vars]}

        \<^item> @{thm unat_mod_distrib [no_vars]}

        \<^item> @{thm [mode=iff] udvd_iff_dvd [no_vars]}

    \<^item> Operations with with signed interpretation of words:

        \<^item> @{thm [mode=iff] word_sle_eq [no_vars]}

        \<^item> @{thm [mode=iff] word_sless_alt [no_vars]}

        \<^item> @{thm sint_signed_drop_bit_eq [no_vars]}

    \<^item> Rotation and reversal:

        \<^item> @{term [source] \<open>word_rotl :: nat \<Rightarrow> 'a::len word \<Rightarrow> 'a word\<close>}

        \<^item> @{term [source] \<open>word_rotr :: nat \<Rightarrow> 'a::len word \<Rightarrow> 'a word\<close>}

        \<^item> @{term [source] \<open>word_roti :: int \<Rightarrow> 'a::len word \<Rightarrow> 'a word\<close>}

        \<^item> @{term [source] \<open>word_reverse :: 'a::len word \<Rightarrow> 'a word\<close>}

    \<^item> Concatenation: @{term [source, display] \<open>word_cat :: 'a::len word \<Rightarrow> 'b::len word \<Rightarrow> 'c::len word\<close>}

  For proofs about words the following default strategies are applicable:

    \<^item> Using bit extensionality (facts \<^text>\<open>bit_eq_iff\<close>, \<^text>\<open>bit_eqI\<close>).

    \<^item> Using the @{method transfer} method.
\<close>

subsection \<open>More theories\<close>

text \<open>
  Note: currently, the theories listed here are hardly separate
  entites since they import each other in various ways.
  Always inspect them to understand what you pull in if you
  want to import one.

    \<^descr>[Syntax]

      \<^descr>[\<^theory>\<open>Word_Lib.Hex_Words\<close>]
        Printing word numerals as hexadecimal numerals.

      \<^descr>[\<^theory>\<open>Word_Lib.Word_Type_Syntax\<close>]
        Pretty type-sensitive syntax for cast operations.

      \<^descr>[\<^theory>\<open>Word_Lib.Word_Syntax\<close>]
        Specific ASCII syntax for prominent bit operations on word.

    \<^descr>[Proof tools]

      \<^descr>[\<^theory>\<open>Word_Lib.Norm_Words\<close>]
        Rewriting word numerals to normal forms.

      \<^descr>[\<^theory>\<open>Word_Lib.Bitwise\<close>]
        Method @{method word_bitwise} decomposes word equalities and inequalities into bit propositions.

      \<^descr>[\<^theory>\<open>Word_Lib.Word_EqI\<close>]
        Method @{method word_eqI_solve} decomposes word equalities and inequalities into bit propositions.

    \<^descr>[Operations]

      \<^descr>[\<^theory>\<open>Word_Lib.Word_Lib\<close>]
        Various operations on word, particularly:

          \<^item> @{term [source] \<open>(sdiv) :: 'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>}

          \<^item> @{term [source] \<open>(smod) :: 'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>}

      \<^descr>[\<^theory>\<open>Word_Lib.Aligned\<close>] \

          \<^item> @{thm [mode=iff] is_aligned_iff_udvd [no_vars]}

      \<^descr>[\<^theory>\<open>Word_Lib.Word_Next\<close>] \

          \<^item> @{thm word_next_unfold [no_vars]}

          \<^item> @{thm word_prev_unfold [no_vars]}

    \<^descr>[Types]

      \<^descr>[\<^theory>\<open>Word_Lib.Signed_Words\<close>]

          Formal tagging of word types with a \<^text>\<open>signed\<close> marker;
          currently it is not clear what practical relevance
          this bears.

    \<^descr>[Mechanisms]

      \<^descr>[\<^theory>\<open>Word_Lib.Word_Enum\<close>]

          More on explicit enumeration of word types.

    \<^descr>[Lemmas]

      Collections of lemmas:

      \<^descr>[\<^theory>\<open>Word_Lib.Word_Lemmas\<close>] generic.

      \<^descr>[\<^theory>\<open>Word_Lib.Word_Lemmas_32\<close>] for 32-bit words.

      \<^descr>[\<^theory>\<open>Word_Lib.Word_Lemmas_64\<close>] for 64-bit words.
\<close>


subsection \<open>Legacy theories\<close>

text \<open>
  The following theories contain material which has been
  factored out since it is not recommended to use it in
  new applications, mostly because matters can be expressed
  succinctly using already existing operations.

  This section gives some indication how to migrate away
  from those theories.  However theorem coverage may still
  be terse in some cases.

  \<^descr>[\<^theory>\<open>HOL-Word.Misc_lsb\<close>]

    A mere alias: @{thm [mode=iff] lsb_odd [where ?'a = int, no_vars]}

  \<^descr>[\<^theory>\<open>HOL-Word.Misc_msb\<close>]

    An alias for the most significant bit; suggested replacements:

      \<^item> @{thm [mode=iff] msb_int_def [of k]}

      \<^item> @{thm [mode=iff] word_msb_sint [no_vars]}

      \<^item> @{thm [mode=iff] msb_word_iff_sless_0 [no_vars]}

      \<^item> @{thm [mode=iff] msb_word_iff_bit [no_vars]}

  \<^descr>[\<^theory>\<open>HOL-Word.Misc_set_bit\<close>]

    An alias: @{thm set_bit_eq [no_vars]}

  \<^descr>[\<^theory>\<open>HOL-Word.Misc_Typedef\<close>]

    An invasive low-level extension to HOL typedef to provide
    conversions along type morphisms.

  \<^descr>[\<^theory>\<open>HOL-Word.Traditional_Syntax\<close>]

    Clones of existing operations decorated with
    traditional syntax:

      \<^item> @{thm test_bit_eq_bit [no_vars]}

      \<^item> @{thm shiftl_eq_push_bit [no_vars]}

      \<^item> @{thm shiftr_eq_drop_bit [no_vars]}

  \<^descr>[\<^theory>\<open>HOL-Word.Reversed_Bit_Lists\<close>]

    Representation of bit values as explicit list in
    \<^emph>\<open>reversed\<close> order.

    This should rarely be necessary: the \<^const>\<open>bit\<close> projection
    should be sufficient in most cases.  In case explicit lists
    are needed, existing operations can be used:

    @{thm [display] horner_sum_bit_eq_take_bit [where ?'a = int, no_vars]}
\<close>

(*<*)
end
(*>*)
