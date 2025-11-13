(*  Title:      Zippy/zippy_base_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_BASE_BASE = \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_UTIL"\<close>

functor Zippy_Base_Base(A : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_UTIL"\<close>) : ZIPPY_BASE_BASE = A