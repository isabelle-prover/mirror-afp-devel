theory R_R_Spark_Declaration
imports Complex_Main

begin

type_synonym block_index' = " int "
type_synonym round_index' = " int "
type_synonym block_permutation' = " int => int "
consts block_index__base__first'' :: " int "
consts block_index__base__last'' :: " int "
consts block_index__first'' :: " int "
consts block_index__last'' :: " int "
consts block_index__size'' :: " int "
consts block_permutation___default_arr'' :: 
" block_permutation'
"
consts block_permutation___default_arr_element'' :: " int "
consts j'' :: " int "
consts j___init'' :: " int "
consts j___loopinit'' :: " int "
consts r_values'' :: " block_permutation' "
consts round_index__base__first'' :: " int "
consts round_index__base__last'' :: " int "
consts round_index__first'' :: " int "
consts round_index__last'' :: " int "
consts round_index__size'' :: " int "
consts bit__not' :: " [ int , int ] => int "
consts block_permutation___mk_const_arr' :: 
" int => block_permutation'
"
consts character__pos' :: " int => int "
consts character__val' :: " int => int "
consts int___abs' :: " int => int "
consts int___div' :: " [ int , int ] => int "
consts int___exp' :: " [ int , int ] => int "
consts int___mod' :: " [ int , int ] => int "
consts int___odd' :: " int => bool "
consts int___rem' :: " [ int , int ] => int "
consts int___times' :: " [ int , int ] => int "
consts int___to_real' :: " int => real "
consts real___abs' :: " real => real "
consts real___div' :: " [ real , real ] => real "
consts real___exp' :: " [ real , int ] => real "
consts real___minus' :: " [ real , real ] => real "
consts real___plus' :: " [ real , real ] => real "
consts real___times' :: " [ real , real ] => real "
consts real___uminus' :: " real => real "
consts round__' :: " real => int "

end
