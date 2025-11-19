use "src/product_construction/ir_types/build.sml";
use "src/product_construction/ceiling_util/build.sml";
Build.subdir "src/product_construction/"
             [
               "rewrite_bexps", "renaming","constraints",
               "ceiling", "local_ceiling", "funs", "single_automaton", "product_transition",
               "transition_composition", "construction"
             ]
