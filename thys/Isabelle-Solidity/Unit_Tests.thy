theory Unit_Tests
imports Solidity "HOL-Library.Code_Target_Numeral" "HOL-Library.Code_Target_Nat" "HOL-Library.Code_Target_Int"
begin

section \<open>Examples\<close>

definition "vt_true = Bool True"
definition "vt_false = Bool False"
definition "vt_sint_m10 = Uint (-10)"
definition "vt_sint_0 = Uint 0"
definition "vt_sint_1 = Uint 1"
definition "vt_sint_2 = Uint 2"
definition "vt_sint_10 = Uint 10"
definition "vt_address = Address null"

definition "sd_true = storage_data.Value vt_true"
definition "sd_false = storage_data.Value vt_false"
definition "sd_sint8_m10 = storage_data.Value vt_sint_m10"
definition "sd_uint8_10 = storage_data.Value vt_sint_10"
definition "sd_address = storage_data.Value vt_address"
definition "(sd_Array_3_true::aspace valtype storage_data) = storage_data.Array [sd_true,sd_true,sd_true]"
definition "(sd_Array_3_false::aspace valtype storage_data) = storage_data.Array [sd_false,sd_false,sd_false]"
definition "(sd_Array_2_3_true_false::aspace valtype storage_data) = storage_data.Array [sd_Array_3_true, sd_Array_3_false]"
definition "(sd_Array_2_3_false_false::aspace valtype storage_data) = storage_data.Array [sd_Array_3_false, sd_Array_3_false]"

definition "md_true = mdata.Value vt_true"
definition "md_false = mdata.Value vt_false"
definition "md_sint_m10 = mdata.Value vt_sint_m10"
definition "md_uint_10 = mdata.Value vt_sint_10"
definition "md_address = mdata.Value vt_address"
definition "mem_Array_2_3_true_false = [md_true,md_true,md_true,mdata.Array [0,1,2],md_false,md_false,md_false,mdata.Array [4,5,6],mdata.Array [3,7]]"
definition "mem_Array_2_3_false_false = [md_false,md_false,md_false,mdata.Array [0,1,2],md_false,md_false,md_false,mdata.Array [4,5,6],mdata.Array [3,7]]"
definition "mem_sint_m10_uint_10= [md_sint_m10,md_uint_10]"

definition "cd_true = call_data.Value vt_true"
definition "cd_false = call_data.Value vt_false"
definition "cd_sint8_m10 = call_data.Value vt_sint_m10"
definition "cd_uint8_10 = call_data.Value vt_sint_10"
definition "cd_address = call_data.Value vt_address"
definition "cd_Array_3_true = call_data.Array [cd_true,cd_true,cd_true]"
definition "cd_Array_3_false = call_data.Array [cd_false,cd_false,cd_false]"
definition "cd_Array_2_3_true_false = call_data.Array [cd_Array_3_true, cd_Array_3_false]"
definition "cd_Array_2_3_false_false = call_data.Array [cd_Array_3_false, cd_Array_3_false]"

(*
  Tested with v0.8.25
*)

global_interpretation method: Method A1 250 100
  defines method_sender_monad = method.sender_monad
      and method_value_monad  = method.value_monad
      and method_timestamp_monad  = method.block_timestamp_monad
  by standard (simp add: null_def)

global_interpretation contract: Contract A1 
  defines contract_assign_stack_monad = contract.assign_stack_monad
      and contract_assign_stack       = contract.assign_stack
      and contract_stackLookup        = contract.stackLookup
      and contract_storeLookup        = contract.storeLookup
      and contract_assign_storage_monad = contract.assign_storage_monad
      and contract_assign_storage = contract.assign_storage
      and contract_storage_update_monad = contract.storage_update_monad
      and contract_storage_update = contract.storage_update
      and contract_this_monad = contract.this_monad
      and contract_storearrayLength = contract.storeArrayLength
      and contract_arrayLength = contract.arrayLength
      and contract_allocate = contract.allocate
  .

global_interpretation keccak256: Keccak256 id
  defines keccak256_keccak256_monad = keccak256.keccak256_monad
  by standard simp

section "States"

definition emptyState::"aspace state" where
"emptyState =
  \<lparr>
    state.Memory = [],
    state.Calldata = fmempty,
    state.Storage = (\<lambda>_ _. undefined),
    state.Stack = fmempty,
    state.Balances = (\<lambda>_. 0)
  \<rparr>"

definition m where 
  "m = [md_true,
        md_true,
        md_true,
        mdata.Array [0,1,2],
        md_false,
        md_false,
        md_false,
        mdata.Array [4,5,6],
        mdata.Array [3,7],
        md_true,
        md_true,
        md_true,
      mdata.Array [9,10,11]]"

definition m' where
  "m' = [md_true,
        md_true,
        md_true,
        mdata.Array [9,10,11],
        md_false,
        md_false,
        md_false,
        mdata.Array [4,5,6],
        mdata.Array [3,7],
        md_true,
        md_true,
        md_true,
      mdata.Array [9,10,11]]"
definition "mystack = fmap_of_list [(STR ''x'', kdata.Memory 8), (STR ''y'', kdata.Memory 12)]"
definition "mystate = emptyState\<lparr>Stack := mystack, Memory := m\<rparr>"

section "Constants"

lemma "P (execute true_monad emptyState)
     = P (Normal (rvalue.Value (Bool True),emptyState))"
  by (normalization,simp)

lemma "P (execute false_monad emptyState)
     = P (Normal (rvalue.Value (Bool False),emptyState))"
  by (normalization,simp)

lemma "P (execute (sint_monad 5) emptyState)
     = P (Normal (rvalue.Value (Uint 5),emptyState))"
  by (normalization, simp)

lemma "P (execute (address_monad A5) emptyState)
     = P (Normal (rvalue.Value (Address A5),emptyState))"
  by (normalization,simp)

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (contract_this_monad) (address_monad A1))
      }) emptyState)"
  by (normalization)

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (method_sender_monad) (address_monad A1))
      }) emptyState)"
  by (normalization)

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (method_value_monad) (sint_monad 250))
      }) emptyState)"
  by (normalization)

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (method_timestamp_monad) (sint_monad 100))
      }) emptyState)"
  by (normalization)

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (keccak256_keccak256_monad (sint_monad 5)) (sint_monad 5))
      }) emptyState)"
  by (normalization)

section "Basic Operators"

subsection "Not monad"
(*
  pragma solidity = 0.8.25;
  
  contract Test {
    function test1() public {
        assert (!true == false);
    }

    function test2() public {
        assert (!false == true);
    }
  }
*)

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (not_monad true_monad) false_monad)
      }) emptyState)"
  by (normalization)

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (not_monad false_monad) true_monad)
      }) emptyState)"
  by (normalization)

subsection "Equals monad"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      function test() public {
          assert (10 == 100);
      }
  }
*)

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (sint_monad 10) (sint_monad 10))
      }) emptyState)"
  by (normalization)

subsection "Less monad"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      function test() public {
          assert (10 < 100);
      }
  }
*)

lemma "is_Normal (execute (do {
        assert_monad (less_monad (sint_monad 10) (sint_monad 11))
      }) emptyState)"
  by (normalization)

subsection "And monad"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      function test() public {
        assert (true && false == false);
      }
  }
*)

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (and_monad (true_monad) (false_monad)) (false_monad))
      }) emptyState)"
  by (normalization)

subsection "Or monad"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      function test() public {
        assert (true || false == true);
      }
  }
*)

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (or_monad (true_monad) (false_monad)) (true_monad))
      }) emptyState)"
  by (normalization)

subsection "Plus monad"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
    function test1() public {
      unchecked{ assert(5 + 6 == 11); }
    }

    function test2() public {
      unchecked{ assert(2**256-1 + uint256 (6) == 5); }
    }
  }
*)

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (plus_monad (sint_monad 5) (sint_monad 6)) (sint_monad 11))
      }) emptyState)"
  by (normalization)

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (plus_monad (sint_monad (2^256 - 1)) (sint_monad 6)) (sint_monad 5))
      }) emptyState)"
  by (normalization)

subsection "Plus monad safe"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
    function test1() public {
      assert(5 + 6 == 11);
    }

    function test2() public {
      assert(2**256-1 + uint256(6) == 5);
    }
  }
*)

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (plus_monad_safe (sint_monad 5) (sint_monad 6)) (sint_monad 11))
      }) emptyState)"
  by (normalization)

lemma "is_Exception (execute (do {
        assert_monad (equals_monad (plus_monad_safe (sint_monad (2^256 - 1)) (sint_monad 6)) (sint_monad 5))
      }) emptyState)"
  by (normalization)

subsection "Minus monad"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
    function test1() public {
        unchecked {assert(6 - 5 == 1);}
    }

    function test2() public {
        unchecked {assert(uint256(5) - uint256(10) == uint256(2**256-5));}
    }
  }
*)

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (minus_monad (sint_monad 6) (sint_monad 5)) (sint_monad 1))
      }) emptyState)"
  by (normalization)

subsection "Minus monad safe"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
    function test1() public {
        unchecked {assert(6 - 5 == 1);}
    }

    function test2() public {
        unchecked {assert(uint256(5) - uint256(10) == uint256(2**256-5));}
    }
  }
*)

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (minus_monad_safe (sint_monad 6) (sint_monad 5)) (sint_monad 1))
      }) emptyState)"
  by (normalization)

lemma "is_Exception (execute (do {
        assert_monad (equals_monad (minus_monad_safe (sint_monad 5) (sint_monad 6)) (sint_monad (2^256 - 5)))
      }) emptyState)"
  by (normalization)

subsection "Mult monad"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
    function test1() public {
      unchecked { assert(5 * 6 == 30); }
    }

    function test2() public {
      unchecked { assert (uint256(2**255) * uint256(2) == uint256(0)); }
    }
  }
*)

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (mult_monad (sint_monad 5) (sint_monad 6)) (sint_monad 30))
      }) emptyState)"
  by (normalization)

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (mult_monad (sint_monad (2^255)) (sint_monad 2)) (sint_monad 0))
      }) emptyState)"
  by (normalization)

subsection "Mult monad safe"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
    function test1() public {
      assert(5 * 6 == 30);
    }

    function test2() public {
      assert (uint256(2**255) * uint256(2) == uint256(0));
    }
  }
*)

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (mult_monad_safe (sint_monad 5) (sint_monad 6)) (sint_monad 30))
      }) emptyState)"
  by (normalization)

lemma "is_Exception (execute (do {
        assert_monad (equals_monad (mult_monad_safe (sint_monad (2^255)) (sint_monad 2)) (sint_monad 0))
      }) emptyState)"
  by (normalization)

subsection "Mod monad"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
    function test() public {
      assert(9 % 5 == 4);
    }
  }
*)

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (mod_monad (sint_monad 9) (sint_monad 5)) (sint_monad 4))
      }) emptyState)"
  by (normalization)

section "Store lookup"

subsection "Value type"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      uint x = 5;
  
      function test() public {
        assert(x == 5);
      }
  }
*)
definition "pstorage1 = (\<lambda>_. undefined) (STR ''x'' := storage_data.Value (Uint 5))"
definition "storage1 = (\<lambda>_. undefined) (A1 := pstorage1)"
definition "state1 = emptyState\<lparr>Storage := storage1\<rparr>"

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (contract_storeLookup (STR ''x'') []) (sint_monad 5))
      }) state1)" by normalization

subsection "Array"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      uint[1] x = [5];
  
      function test() public {
          assert(x[0] == 5);
      }
  }
*)

definition "pstorage2 = (\<lambda>_. undefined) (STR ''x'' := storage_data.Array [storage_data.Value (Uint 5)])"
definition "storage2 = (\<lambda>_. undefined) (A1 := pstorage2)"
definition "state2 = emptyState\<lparr>Storage := storage2\<rparr>"

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (contract_storeLookup (STR ''x'') [sint_monad 0]) (sint_monad 5))
      }) state2)" by normalization

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      uint[1][1] x = [[5]];
  
      function test() public {
          assert(x[0][0] == 5);
      }
  }
*)

definition "pstorage20 = (\<lambda>_. undefined) (STR ''x'' := storage_data.Array [storage_data.Array [storage_data.Value (Uint 5)]])"
definition "storage20 = (\<lambda>_. undefined) (A1 := pstorage20)"
definition "state20 = emptyState\<lparr>Storage := storage20\<rparr>"

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (contract_storeLookup (STR ''x'') [sint_monad 0, sint_monad 0]) (sint_monad 5))
      }) state20)" by normalization

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      uint[1][1] x = [[5]];
      uint[1][1] y = [[5]];
  
      function test() public {
          assert(x[0][0] == y[0][0]);
      }
  }
*)

definition "pstorage21 = pstorage20 (STR ''y'' := storage_data.Array [storage_data.Array [storage_data.Value (Uint 5)]])"
definition "storage21 = (\<lambda>_. undefined) (A1 := pstorage21)"
definition "state21 = emptyState\<lparr>Storage := storage21\<rparr>"

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (contract_storeLookup (STR ''x'') [sint_monad 0, sint_monad 0]) (contract_storeLookup (STR ''y'') [sint_monad 0, sint_monad 0]))
      }) state21)" by normalization

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      uint[1][1] x = [[5]];
      uint[1][1] y = [[5]];
  
      function test() public {
          assert(x[0] == y[0]); //Compiler error
      }
  }
*)

lemma "is_Exception (execute (do {
        assert_monad (equals_monad (contract_storeLookup (STR ''x'') [sint_monad 0]) (contract_storeLookup (STR ''y'') [sint_monad 0]))
      }) state21)" by normalization

subsubsection "Mappings"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      mapping (uint => uint) x;
  
      constructor () public {
          x[0] = 5;
      }
  
      function test() public {
          assert(x[0] == 5);
      }
  }
*)

definition "pstorage3 = (\<lambda>_. undefined) (STR ''x'' := storage_data.Map ((\<lambda>_. undefined) (Uint (0) := storage_data.Value (Uint 5))))"
definition "storage3 = (\<lambda>_. undefined) (A1 := pstorage3)"
definition "state3 = emptyState\<lparr>Storage := storage3\<rparr>"

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (contract_storeLookup (STR ''x'') [sint_monad 0]) (sint_monad 5))
      }) state3)" by normalization

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      mapping (uint => mapping (bool => uint)) x;
  
      constructor () public {
          x[0][false] = 5;
      }
  
      function test() public {
          assert(x[0][false] == 5);
      }
  }
*)

definition "pstorage30 = (\<lambda>_. undefined) (STR ''x'' := storage_data.Map ((\<lambda>_. undefined) (Uint 0 := storage_data.Map ((\<lambda>_. undefined) (Bool False := (storage_data.Value (Uint 5)))))))"
definition "storage30 = (\<lambda>_. undefined) (A1 := pstorage30)"
definition "state30 = emptyState\<lparr>Storage := storage30\<rparr>"

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (contract_storeLookup (STR ''x'') [sint_monad 0, false_monad]) (sint_monad 5))
      }) state30)" by normalization

section "Stack lookup"

subsection "Value type"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      function test() public {
          uint x = 5;
          assert(x == 5);
      }
  }
*)

lemma "is_Normal (execute (do {
        init (Uint 5) (STR ''x'');
        assert_monad (equals_monad (contract_stackLookup (STR ''x'') []) (sint_monad 5))
      }) emptyState)" by normalization

subsection "Memory"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      function test() public {
          uint[1] memory x = [uint256(5)];
          assert(x[0] == 5);
      }
  }
*)

lemma "is_Normal (execute (do {
        write (adata.Array [adata.Value (Uint 5)]) (STR ''x'');
        assert_monad (equals_monad (contract_stackLookup (STR ''x'') [sint_monad 0]) (sint_monad 5))
      }) emptyState)" by normalization

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      function test() public {
          uint[1][1] memory x = [[uint256(5)]];
          uint[1] memory y = x[0];
          assert(y[0] == 5);
      }
  }
*)

lemma "is_Normal (execute (do {
        write (adata.Array [adata.Array [adata.Value (Uint 5)]]) (STR ''x'');
        write (adata.Array [adata.Value (Uint 0)]) (STR ''y'');
        contract_assign_stack_monad (STR ''y'') [] (contract_stackLookup (STR ''x'') [sint_monad 0]);
        assert_monad (equals_monad (contract_stackLookup (STR ''y'') [sint_monad 0]) (sint_monad 5))
      }) emptyState)" by normalization

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      function test() public {
          uint[1][1] memory x = [[uint256(5)]];
          uint[1][1] memory y;
          y[0] = x [0];
          assert(x[0][0] == 5);          
          assert(y[0][0] == 5);
      }
  }
*)

lemma "is_Normal (execute (do {
        write (adata.Array [adata.Array [adata.Value (Uint 5)]]) (STR ''x'');
        write (adata.Array [adata.Value (Uint 0)]) (STR ''y'');
        contract_assign_stack_monad (STR ''y'') [sint_monad 0] (contract_stackLookup (STR ''x'') [sint_monad 0]);
        assert_monad (equals_monad (contract_stackLookup (STR ''x'') [sint_monad 0, sint_monad 0]) (sint_monad 5));
        assert_monad (equals_monad (contract_stackLookup (STR ''y'') [sint_monad 0, sint_monad 0]) (sint_monad 5))
      }) emptyState)" by normalization

subsection "Calldata"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      function test(uint[1] calldata x) public {
          require (x[0] == 5, "Testcase requires x[0] == 5");
          assert (x[0] == 5);
      }
  }
*)

lemma "is_Normal (execute (do {
        cinit (call_data.Array [call_data.Value (Uint 5)]) (STR ''x'');
        assert_monad (equals_monad (contract_stackLookup (STR ''x'') [sint_monad 0]) (sint_monad 5))
      }) emptyState)" by normalization

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      function test(uint[1][1] calldata x) public {
          require (x[0][0] == 5, "Testcase requires x[0] == 0");
          uint[1] calldata y = x[0]; 
          assert (y[0] == 5);
      }
  }
*)


definition "pcalldata71 = fmap_of_list [(STR ''x'', call_data.Array [call_data.Array [call_data.Value (Uint 5)]])]"
definition "pstack71 = fmap_of_list [(STR ''y'', kdata.Calldata (Some \<lparr>Location = STR ''x'', Offset = [Uint 0]\<rparr>))]"
definition "state71 = emptyState\<lparr>Calldata := pcalldata71, Stack:=pstack71\<rparr>"
lemma "is_Normal (execute (do {
        assert_monad (equals_monad (contract_stackLookup (STR ''y'') [sint_monad 0]) (sint_monad 5))
      }) state71)" by normalization

subsubsection "Storage pointers"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      uint[1] x = [5];
  
      function test() public {
          uint[1] storage y = x;
          assert (y[0] == 5);
      }
  }
*)

definition "pstorage8 = (\<lambda>_. undefined) (STR ''x'' := storage_data.Array [storage_data.Value (Uint 5)])"
definition "storage8 = (\<lambda>_. undefined) (A1 := pstorage8)"
definition "stack8 = fmap_of_list [(STR ''y'', kdata.Storage (Some \<lparr>Location = STR ''x'', Offset= []\<rparr>))]"
definition "state8 = emptyState\<lparr>Storage := storage8, Stack := stack8\<rparr>"

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (contract_stackLookup (STR ''y'') [sint_monad 0]) (sint_monad 5))
      }) state8)" by normalization

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      uint[1][1] x = [[5]];
  
      function test() public {
          uint[1] storage y = x[0];
          assert (y[0] == 5);
      }
  }
*)

definition "pstorage9 = (\<lambda>_. undefined) (STR ''x'' := storage_data.Array [storage_data.Array [storage_data.Value (Uint 5)]])"
definition "storage9 = (\<lambda>_. undefined) (A1 := pstorage9)"
definition "stack9 = fmap_of_list [(STR ''y'', kdata.Storage (Some \<lparr>Location = STR ''x'', Offset= [Uint 0]\<rparr>))]"
definition "state9 = emptyState\<lparr>Storage := storage9, Stack := stack9\<rparr>"

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (contract_stackLookup (STR ''y'') [sint_monad 0]) (sint_monad 5))
      }) state9)" by normalization

subsection "Arrays"

subsubsection "Storage Arrays"

paragraph "Length"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      uint[1] x = [5];
  
      function test() public {
          assert (x.length == 1);
      }
  }
*)

definition "pstorage10 = (\<lambda>_. undefined) (STR ''x'' := storage_data.Array [storage_data.Value (Uint 5)])"
definition "storage10 = (\<lambda>_. undefined) (A1 := pstorage10)"
definition "state10 = emptyState\<lparr>Storage := storage10\<rparr>"

paragraph "Push"

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (contract_storearrayLength (STR ''x'') []) (sint_monad 1))
      }) state10)" by normalization

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      uint[] x = [5];
  
      function test() public {
          x.push(uint(6));
          assert (x[0] == 5);
          assert (x[1] == 6);
      }
  }
*)

definition "pstorage11 = (\<lambda>_. undefined) (STR ''x'' := storage_data.Array [storage_data.Value (Uint 5)])"
definition "storage11 = (\<lambda>_. undefined) (A1 := pstorage11)"
definition "state11 = emptyState\<lparr>Storage := storage11\<rparr>"

lemma "is_Normal (execute (do {
        contract_allocate (STR ''x'') [] (storage_data.Value (Uint 6));
        assert_monad (equals_monad (contract_storeLookup (STR ''x'') [sint_monad 0]) (sint_monad 5));
        assert_monad (equals_monad (contract_storeLookup (STR ''x'') [sint_monad 1]) (sint_monad 6))
      }) state11)" by normalization

subsubsection "Memory Arrays"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      function test() public {
          uint[1] memory x = [1];
          assert (x.length == 1);
          assert (x[0] == 1);
      }
  }
*)

lemma "is_Normal (execute (do {
        write (adata.Array [adata.Value (Uint 1)]) (STR ''x'');
        assert_monad (equals_monad (contract_arrayLength (STR ''x'') []) (sint_monad 1));
        assert_monad (equals_monad (contract_stackLookup (STR ''x'') [sint_monad 0]) (sint_monad 1))
      }) emptyState)" by normalization

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      function test() public {
          uint[1] memory x = [[1]];
          assert (x.length == 1);
          assert (x[0].length == 1);
          assert (x[0][0] == 1);
      }
  }
*)

lemma "is_Normal (execute (do {
        write (adata.Array [adata.Array [adata.Value (Uint 1)]]) (STR ''x'');
        assert_monad (equals_monad (contract_arrayLength (STR ''x'') []) (sint_monad 1));
        assert_monad (equals_monad (contract_arrayLength (STR ''x'') [sint_monad 0]) (sint_monad 1));
        assert_monad (equals_monad (contract_stackLookup (STR ''x'') [sint_monad 0, sint_monad 0]) (sint_monad 1))
      }) emptyState)" by normalization

subsubsection "Calldata Arrays"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      function test(uint[1] calldata x) public {
          assert (x.length == 1);
      }
  }
*)

lemma "is_Normal (execute (do {
        cinit (call_data.Array [call_data.Array [call_data.Value (Uint 5)]]) (STR ''x'');
        assert_monad (equals_monad (contract_arrayLength (STR ''x'') []) (sint_monad 1))
      }) emptyState)" by normalization

subsubsection "Storage pointer Arrays"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      uint[1] x = [5];
  
      function test() public {
          uint[1] storage y = x;
          assert (y.length == 1);
      }
  }
*)

definition "pstorage14 = (\<lambda>_. undefined) (STR ''x'' := storage_data.Array [storage_data.Value (Uint 5)])"
definition "storage14 = (\<lambda>_. undefined) (A1 := pstorage14)"
definition "stack14 = fmap_of_list [(STR ''y'', kdata.Storage (Some \<lparr>Location = STR ''x'', Offset= []\<rparr>))]"
definition "state14 = emptyState\<lparr>Storage := storage14, Stack := stack14\<rparr>"

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (contract_arrayLength (STR ''y'') []) (sint_monad 1))
      }) state14)" by normalization

section "Conditionals"
(*
  pragma solidity =0.8.25;
  
  contract Test {
      function test0() public {
          uint x = 0;
          if (true) {
              x = 1;
          } else {
              x = 2;
          }
          assert (x == 1);
      }
  
      function test1() public {
          uint x = 0;
          if (false) {
              x = 1;
          } else {
              x = 2;
          }
          assert (x == 2);
      }
  }
*)

lemma "is_Normal (execute (do {
        init (Uint 0) (STR ''x'');
        cond_monad (true_monad)
          (contract_assign_stack_monad (STR ''x'') [] (sint_monad 1))
          (contract_assign_stack_monad (STR ''x'') [] (sint_monad 2));
        assert_monad (equals_monad (contract_stackLookup (STR ''x'') []) (sint_monad 1))
      }) emptyState)"
  by (normalization)

lemma "is_Normal (execute (do {
        init (Uint 0) (STR ''x'');
        cond_monad (false_monad)
          (contract_assign_stack_monad (STR ''x'') [] (sint_monad 1))
          (contract_assign_stack_monad (STR ''x'') [] (sint_monad 2));
        assert_monad (equals_monad (contract_stackLookup (STR ''x'') []) (sint_monad 2))
      }) emptyState)"
  by (normalization)

section "Assignments"

subsection "Stack Value to Stack Value"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      function test() public {
          uint x=0;
          uint y=x;
          y = 1;
          assert (x == 0);
          assert (y == 1);
      }
  }
*)

lemma "is_Normal (execute (do {
        init (Uint 0) (STR ''x'');
        init (Uint 0) (STR ''y'');
        contract_assign_stack_monad (STR ''y'') [] (sint_monad 1);
        assert_monad (equals_monad (contract_stackLookup (STR ''x'') []) (sint_monad 0));
        assert_monad (equals_monad (contract_stackLookup (STR ''y'') []) (sint_monad 1))
      }) emptyState)"
  by (normalization)

subsection "Memory Array to Memory Array"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      function test() public {
          uint[1] memory x = [0];
          uint[1] memory y = [0];
          y = x;
          x[0] = 1;
          assert (x[0] == 1);
          assert (y[0] == 1);
      }
  }
*)

lemma "is_Normal (execute (do {
        write (adata.Array [adata.Value (Uint 0)]) (STR ''x'');
        write (adata.Array [adata.Value (Uint 0)]) (STR ''y'');
        contract_assign_stack_monad (STR ''y'') [] (contract_stackLookup (STR ''x'') []);
        contract_assign_stack_monad  (STR ''x'') [sint_monad 0] (sint_monad 1);
        assert_monad (equals_monad (contract_stackLookup (STR ''x'') [sint_monad 0]) (sint_monad 1));
        assert_monad (equals_monad (contract_stackLookup (STR ''y'') [sint_monad 0]) (sint_monad 1))
      }) emptyState)"
  by (normalization)

subsection "Calldata Array to Memory Array"
(*
  pragma solidity =0.8.25;
  
  contract Test {
      function test(uint[1] calldata x) public {
          require (x[0] == 0, "Testcase requires x[0] == 0");

          uint[1] memory y = [0];
  
          y = x;
          y[0] = 1;
  
          assert (x[0] == 0);
          assert (y[0] == 1);
      }
  }
*)

lemma "is_Normal (execute (do {
        cinit (call_data.Array [call_data.Value (Uint 0)]) (STR ''x'');
        write (adata.Array [adata.Value (Uint 0)]) (STR ''y'');
        require_monad (equals_monad (contract_stackLookup (STR ''x'') [sint_monad 0]) (sint_monad 0));
        contract_assign_stack_monad (STR ''y'') [] (contract_stackLookup (STR ''x'') []);
        contract_assign_stack_monad  (STR ''y'') [sint_monad 0] (sint_monad 1);
        assert_monad (equals_monad (contract_stackLookup (STR ''x'') [sint_monad 0]) (sint_monad 0));
        assert_monad (equals_monad (contract_stackLookup (STR ''y'') [sint_monad 0]) (sint_monad 1))
      }) emptyState)"
  by (normalization)

(*
  pragma solidity =0.8.25;
  //demonstrates that assignment creates fresh arrays instead of writing into existing structure

  contract Test {
    function test(uint8[1][1] calldata x) public {
        require (x[0][0] == 0, "Testcase requires x[0] == 0");

        uint8[1][1] memory y = [[1]];
        uint8[1] memory z = y[0];

        y = x;

        assert (z[0] == 1);
        assert (y[0][0] == 0);
    }
  }
*)

lemma "is_Normal (execute (do {
        cinit (call_data.Array [call_data.Array [call_data.Value (Uint 0)]]) (STR ''x'');
        write (adata.Array [adata.Array [adata.Value (Uint 1)]]) (STR ''y'');
        write (adata.Array [adata.Value (Uint 0)]) (STR ''z'');
        contract_assign_stack_monad (STR ''z'') [] (contract_stackLookup (STR ''y'') [sint_monad 0]);
        contract_assign_stack_monad (STR ''y'') [] (contract_stackLookup (STR ''x'') []);
        assert_monad (equals_monad (contract_stackLookup (STR ''z'') [sint_monad 0]) (sint_monad 1));
        assert_monad (equals_monad (contract_stackLookup (STR ''y'') [sint_monad 0, sint_monad 0]) (sint_monad 0))
      }) emptyState)"
  by (normalization)

(*
  pragma solidity =0.8.25;

  contract Test {
    function test(uint8[1][1][1] calldata x) public {
        require (x[0][0][0] == 0, "Testcase requires x[0] == 0");

        uint8[1][1][1] memory y = [[[1]]];
        uint8[1][1] memory z;
        z[0] = y[0][0];

        y[0] = x[0];

        assert (z[0][0] == 1);
        assert (y[0][0][0] == 0);
    }
  }
*)

lemma "is_Normal (execute (do {
        cinit (call_data.Array [call_data.Array [call_data.Array [call_data.Value (Uint 0)]]]) (STR ''x'');
        write (adata.Array [adata.Array [adata.Array [adata.Value (Uint 1)]]]) (STR ''y'');
        write (adata.Array [adata.Array [adata.Value (Uint 0)]]) (STR ''z'');
        contract_assign_stack_monad (STR ''z'') [sint_monad 0] (contract_stackLookup (STR ''y'') [sint_monad 0, sint_monad 0]);
        contract_assign_stack_monad (STR ''y'') [sint_monad 0] (contract_stackLookup (STR ''x'') [sint_monad 0]);
        assert_monad (equals_monad (contract_stackLookup (STR ''z'') [sint_monad 0, sint_monad 0]) (sint_monad 1));
        assert_monad (equals_monad (contract_stackLookup (STR ''y'') [sint_monad 0, sint_monad 0, sint_monad 0]) (sint_monad 0))
      }) emptyState)"
  by (normalization)


subsection "Storage Pointer Array to Memory Array"
(*
  pragma solidity =0.8.25;
  
  contract Test {
      uint[1] s = [uint256 (0)];
  
      function test() public {
          require (s[0] == 0, "Testcase requires s[0] == 0");

          uint[1] storage x = s;
          uint[1] memory y = [uint256 (0)];
  
          y = x;
          y[0] = 1;
  
          assert (x[0] == 0);
          assert (y[0] == 1);
      }
  }
*)

definition "pstorage17 = (\<lambda>_. undefined) (STR ''s'' := storage_data.Array [storage_data.Value (Uint 0)])"
definition "storage17 = (\<lambda>_. undefined) (A1 := pstorage17)"
definition "stack17 = fmap_of_list [(STR ''x'', kdata.Storage (Some \<lparr>Location = STR ''s'', Offset= []\<rparr>))]"
definition "state17 = emptyState\<lparr>Storage := storage17, Stack := stack17\<rparr>"

lemma "is_Normal (execute (do {
        require_monad (equals_monad (contract_storeLookup (STR ''s'') [sint_monad 0]) (sint_monad 0));
        write (adata.Array [adata.Value (Uint 0)]) (STR ''y'');
        contract_assign_stack_monad (STR ''y'') [] (contract_stackLookup (STR ''x'') []);
        contract_assign_stack_monad (STR ''y'') [sint_monad 0] (sint_monad 1);
        assert_monad (equals_monad (contract_stackLookup (STR ''x'') [sint_monad 0]) (sint_monad 0));
        assert_monad (equals_monad (contract_stackLookup (STR ''y'') [sint_monad 0]) (sint_monad 1))
      }) state17)" by normalization

subsection "Storage Array to Memory Array"
(*
  pragma solidity =0.8.25;
  
  contract Test {
      uint[1] x = (0);
  
      function test() public {
        uint[1] memory y = (0);

        y=x;
        y[0] = 1;
        
        assert (x[0] == 0);
        assert (y[0] == 1);
      }
  }
*)

definition "pstorage18 = (\<lambda>_. undefined) (STR ''x'' := storage_data.Array [storage_data.Value (Uint 0)])"
definition "storage18 = (\<lambda>_. undefined) (A1 := pstorage18)"
definition "state18 = emptyState\<lparr>Storage := storage18\<rparr>"

lemma "is_Normal (execute (do {
        write (adata.Array [adata.Value (Uint 0)]) (STR ''y'');
        contract_assign_stack_monad (STR ''y'') [] (contract_storeLookup (STR ''x'') []);
        contract_assign_stack_monad (STR ''y'') [sint_monad 0] (sint_monad 1);
        assert_monad (equals_monad (contract_storeLookup (STR ''x'') [sint_monad 0]) (sint_monad 0));
        assert_monad (equals_monad (contract_stackLookup (STR ''y'') [sint_monad 0]) (sint_monad 1))
      }) state18)" by normalization

(*
  pragma solidity =0.8.25;
  
  contract Test {
      uint[1] x = (1);
  
      function test() public {
        uint[1][1] memory y;

        y[0] = x;
        
        assert (x[0] == 1);
        assert (y[0][0] == 1);
      }
  }
*)

definition "pstorage181 = (\<lambda>_. undefined) (STR ''x'' := storage_data.Array [storage_data.Value (Uint 1)])"
definition "storage181 = (\<lambda>_. undefined) (A1 := pstorage181)"
definition "state181 = emptyState\<lparr>Storage := storage181\<rparr>"

lemma "is_Normal (execute (do {
        write (adata.Array [adata.Array [adata.Value (Uint 0)]]) (STR ''y'');
        contract_assign_stack_monad (STR ''y'') [sint_monad 0] (contract_storeLookup (STR ''x'') []);
        assert_monad (equals_monad (contract_storeLookup (STR ''x'') [sint_monad 0]) (sint_monad 1));
        assert_monad (equals_monad (contract_stackLookup (STR ''y'') [sint_monad 0, sint_monad 0]) (sint_monad 1))
      }) state181)" by normalization

subsection "Storage Pointer Array to Storage Pointer Array"
(*
  pragma solidity =0.8.25;
  
  contract Test {
      uint[1] s1 = (0);
      uint[1] s2 = (0);
  
      function test() public {
          assert (s1[0]==0); //OK
          assert (s2[0]==0); //OK
      
          uint[1] storage x=s1; // this is storage pointer
          uint[1] storage y=s2; // this is storage pointer
      
          y=x;  //y is a pointer to content of s1
          y[0]=1;
      
          assert (s1[0]==1);
          assert (s2[0]==0);
          assert (x[0]==1);
          assert (y[0]==1);
      }
  }
*)

definition "pstorage19 = (\<lambda>_. undefined) (STR ''s1'' := storage_data.Array [storage_data.Value (Uint 0)], STR ''s2'' := storage_data.Array [storage_data.Value (Uint 0)])"
definition "storage19 = (\<lambda>_. undefined) (A1 := pstorage19)"
definition "stack19 = fmap_of_list [
  (STR ''x'', kdata.Storage (Some \<lparr>Location = STR ''s1'', Offset= []\<rparr>)),
  (STR ''y'', kdata.Storage (Some \<lparr>Location = STR ''s2'', Offset= []\<rparr>))
]"
definition "state19 = emptyState\<lparr>Storage := storage19, Stack := stack19\<rparr>"

lemma "is_Normal (execute (do {
        contract_assign_stack_monad (STR ''x'') [] (contract_stackLookup (STR ''y'') []);
        contract_assign_stack_monad (STR ''y'') [sint_monad 0] (sint_monad 1);
        assert_monad (equals_monad (contract_storeLookup (STR ''s1'') [sint_monad 0]) (sint_monad 0));
        assert_monad (equals_monad (contract_storeLookup (STR ''s2'') [sint_monad 0]) (sint_monad 1));
        assert_monad (equals_monad (contract_stackLookup (STR ''x'') [sint_monad 0]) (sint_monad 1));
        assert_monad (equals_monad (contract_stackLookup (STR ''y'') [sint_monad 0]) (sint_monad 1))
      }) state19)" by normalization

subsection "Storage Array to Storage Pointer Array"
(*
  pragma solidity =0.8.25;
  
  contract Test {
      uint[1] s = [0];
  
      function test() public {
        uint[1] storage x; // this is storage pointer
        x=s;
        s[0]=1;
  
        assert (s[0]==1); //OK
        assert (s[0]==0); //OK
        assert (x[0]==1); //OK
      }
  }
*)

definition "pstorage200 = (\<lambda>_. undefined) (STR ''s'' := storage_data.Array [storage_data.Value (Uint 0)])"
definition "storage200 = (\<lambda>_. undefined) (A1 := pstorage200)"
definition "stack200 = fmap_of_list [(STR ''x'', kdata.Storage None)]"
definition "state200 = emptyState\<lparr>Storage := storage200, Stack := stack200\<rparr>"

lemma "is_Normal (execute (do {
        contract_assign_stack_monad (STR ''x'') [] (contract_storeLookup (STR ''s'') []);
        contract_assign_storage_monad (STR ''s'') [sint_monad 0] (sint_monad 1);
        assert_monad (equals_monad (contract_storeLookup (STR ''s'') [sint_monad 0]) (sint_monad 1));
        assert_monad (equals_monad (contract_stackLookup (STR ''x'') [sint_monad 0]) (sint_monad 1))
      }) state200)" by normalization

subsection "Memory Array to Storage Array"
(*
  pragma solidity =0.8.25;
  
  contract Test {
      uint[1] x = (0);
  
      function test() public {
        uint[1] memory y = (0);

        x=y;
        x[0] = 1;
        
        assert (x[0] == 1);
        assert (y[0] == 0);
      }
  }
*)

lemma "is_Normal (execute ( do {
        write (adata.Array [adata.Value (Uint 0)]) (STR ''y'');
        contract_assign_storage_monad (STR ''x'') [] (contract_stackLookup (STR ''y'') []);
        contract_assign_storage_monad (STR ''x'') [sint_monad 0] (sint_monad 1);
        assert_monad (equals_monad (contract_storeLookup (STR ''x'') [sint_monad 0]) (sint_monad 1));
        assert_monad (equals_monad (contract_stackLookup (STR ''y'') [sint_monad 0]) (sint_monad 0))
      }) state200)" by normalization

(*
pragma solidity =0.8.25;
demonstrates that copying to storage uses existing structure instead of allocating new storage.
contract Test {
    uint[1] s = [uint256 (0)];

    function test() public {
        require (s[0] == 0, "Testcase requires s[0] == 0");

        uint[1] storage x = s;
        uint[1] memory y = [uint256 (1)];

        s = y;

        assert (x[0] == 1);
        assert (y[0] == 1);
    }
}
*)

lemma "is_Normal (execute ( do {
        contract_assign_stack_monad (STR ''x'') [] (contract_storeLookup (STR ''s'') []);
        write (adata.Array [adata.Value (Uint 1)]) (STR ''y'');
        contract_assign_storage_monad (STR ''s'') [] (contract_stackLookup (STR ''y'') []);
        assert_monad (equals_monad (contract_stackLookup (STR ''x'') [sint_monad 0]) (sint_monad 1));
        assert_monad (equals_monad (contract_stackLookup (STR ''y'') [sint_monad 0]) (sint_monad 1))
      }) state200)" by normalization

subsection "Calldata Array to Storage Array"
(*
  pragma solidity =0.8.25;
  
  contract Test {
      uint[1] s = [0];
  
      function test(uint[1] calldata x) public {
          require (x[0] == 0, "Testcase requires x[0] == 0");
  
          s = x;
          s[0] = 1;
  
          assert (s[0] == 1);
          assert (x[0] == 0);
      }
  }
*)

definition "pstorage22 = (\<lambda>_. undefined) (STR ''s'' := (storage_data.Array [storage_data.Value (Uint 0)]))"
definition "storage22 = (\<lambda>_. undefined) (A1 := pstorage22)"
definition "state22 = emptyState\<lparr>Storage := storage22\<rparr>"

lemma "is_Normal (execute (do {
        cinit (call_data.Array [call_data.Value (Uint 0)]) (STR ''x'');
        require_monad (equals_monad (contract_stackLookup (STR ''x'') [sint_monad 0]) (sint_monad 0));
        contract_assign_storage_monad (STR ''s'') [] (contract_stackLookup (STR ''x'') []);
        contract_assign_storage_monad (STR ''s'') [sint_monad 0] (sint_monad 1);
        assert_monad (equals_monad (contract_storeLookup (STR ''s'') [sint_monad 0]) (sint_monad 1));
        assert_monad (equals_monad (contract_stackLookup (STR ''x'') [sint_monad 0]) (sint_monad 0))
      }) state22)"
  by (normalization)

subsection "Storage Array to Storage Array"
(*
  pragma solidity =0.8.25;
  
  contract MyToken {
      uint[1] x = [0];
      uint[1] y = [0];
  
      function test() public {
        x=y;
        x[0]=1;

        assert (x[0]==1);
        assert (y[0]==0);
      }
  }
*)

definition "pstorage23 = (\<lambda>_. undefined) (STR ''x'' := (storage_data.Array [storage_data.Value (Uint 0)]), STR ''y'' := (storage_data.Array [storage_data.Value (Uint 0)]))"
definition "storage23 = (\<lambda>_. undefined) (A1 := pstorage23)"
definition "state23 = emptyState\<lparr>Storage := storage23\<rparr>"

lemma "is_Normal (execute ( do {
        contract_assign_storage_monad (STR ''x'') [] (contract_storeLookup (STR ''y'') []);
        contract_assign_storage_monad (STR ''x'') [sint_monad 0] (sint_monad 1);
        assert_monad (equals_monad (contract_storeLookup (STR ''x'') [sint_monad 0]) (sint_monad 1));
        assert_monad (equals_monad (contract_storeLookup (STR ''y'') [sint_monad 0]) (sint_monad 0))
      }) state23)" by normalization

subsection "Storage Array to Memory Array"
(*
  pragma solidity =0.8.25;
  
  contract Test {
      uint[1] x = (1);
  
      function test() public {
        uint[1][1] memory a1;
        uint[1][1] memory a2;
        a2[0] = a1[0];
        a1[0] = x;

        assert (a1[0][0]==1);
        assert (a2[0][0]==0);
    }

  }
*)
definition "pstorage24 = (\<lambda>_. undefined) (STR ''x'' := storage_data.Array [storage_data.Value (Uint 1)])"
definition "storage24 = (\<lambda>_. undefined) (A1 := pstorage24)"
definition "state24 = emptyState\<lparr>Storage := storage24\<rparr>"

lemma "is_Normal (execute (do {
        write (adata.Array [adata.Array [adata.Value (Uint 0)]]) (STR ''a1'');
        write (adata.Array [adata.Array [adata.Value (Uint 0)]]) (STR ''a2'');
        contract_assign_stack_monad (STR ''a2'') [sint_monad 0] (contract_stackLookup (STR ''a1'') [sint_monad 0]);
        contract_assign_stack_monad (STR ''a1'') [sint_monad 0] (contract_storeLookup (STR ''x'') []);
        assert_monad (equals_monad (contract_stackLookup (STR ''a1'') [sint_monad 0, sint_monad 0]) (sint_monad 1));
        assert_monad (equals_monad (contract_stackLookup (STR ''a2'') [sint_monad 0, sint_monad 0]) (sint_monad 0))
      }) state24)" by normalization

section \<open>Declarations\<close>

(*
  pragma solidity =0.8.25;

  contract Test {
      function test() public {
          uint x;
          assert(x == 0);
      }
  }
*)

lemma "is_Normal (execute (do {
        decl TSint (STR ''x'');
        assert_monad (equals_monad (contract_stackLookup (STR ''x'') []) (sint_monad 0))
      }) emptyState)" by normalization

(*
  Declaration of static memory arrays also allocate a new array with default values.

  pragma solidity =0.8.25;
  
  contract Test {
      function test() public {
          uint[1] memory y;
          assert(y[0] == 0);
      }
  }
*)

lemma "is_Normal (execute (do {
        mdecl (TArray 1 (TValue TSint)) (STR ''y'');
        assert_monad (equals_monad (contract_stackLookup (STR ''y'') [sint_monad 0]) (sint_monad 0))
      }) emptyState)" by normalization

(*
  Declaration of dynamic memory arrays also allocate a new empty array.

  pragma solidity =0.8.25;
  
  contract Test {
      function test() public {
          uint[] memory y;
          assert(y[0] == 0); //Runtime error
      }
  }
*)

lemma "state.Memory (snd (normal (execute (do {
        mdecl (DArray (TValue TSint))  (STR ''y'')
      }) emptyState)))=[mdata.Array []]" by normalization

(*
  Declaration of storage pointers do not allocate a new array.

  pragma solidity =0.8.25;
  
  contract Test {
      function test() public {
          uint[1] storage y;
          assert(y[0] == 0); //Compiler error
      }
  }
*)

lemma "is_Exception (execute (do {
        sdecl (SType.TArray 1 (SType.TValue TSint)) (STR ''y'');
        assert_monad (equals_monad (contract_stackLookup (STR ''y'') [sint_monad 0]) (sint_monad 0))
      }) emptyState)" by normalization

(*
  Declaration of calldata pointers do not allocate a new array.

  pragma solidity =0.8.25;
  
  contract Test {
      function test() public {
          uint[1] calldata y;
          assert(y[0] == 0); //Compiler error
      }
  }
*)

(*************************************************************************************)
(* Additional unit tests *)
(*************************************************************************************)

(* Test bytes1, ..., bytes32 *)
(* Missing: constant value assignment *)


(* The following gives compile error - index out of bounds *)
(*
pragma solidity = 0.8.25;

contract Test {
    bytes3 x = hex"112233";

    function test() public view {
        assert(x[3] == 0);
    }
}
*)

(* We only prove that it does not execute normally *)
lemma 
  shows "let pstorage = 
                ((\<lambda>_. undefined) 
                   (STR ''x'' := storage_data.Value (Bytes [CHR 0x01, CHR 0x02, CHR 0x03])));
            storage = (\<lambda>_. undefined) (A1 := pstorage);
            state = emptyState\<lparr>Storage := storage\<rparr>
         in is_Exception (execute (do {
              assert_monad (equals_monad (bytes_index_monad (contract_storeLookup (STR ''x'') []) (sint_monad 3)) (sint_monad 0))
           }) state)"
  by normalization


(*
pragma solidity = 0.8.25;

contract Test {
    bytes3 x;
    bytes3 y = hex"000000";

    function test() public view {
        assert (x[1] == y);
    }
}
*)

lemma 
  shows "let pstorage = 
                ((\<lambda>_. undefined) 
                   (STR ''x'' := storage_data.Value (Bytes [CHR 0xAA, CHR 0xBB, CHR 0xCC])))
                   (STR ''y'' := storage_data.Value (Bytes [CHR 0xBB]));
            storage = (\<lambda>_. undefined) (A1 := pstorage);
            state = emptyState\<lparr>Storage := storage\<rparr>
         in is_Normal (execute (do {
              assert_monad (equals_monad (bytes_index_monad (contract_storeLookup (STR ''x'') []) (sint_monad 1)) (contract_storeLookup (STR ''y'') []))
            }) state)"
  by normalization


(*
pragma solidity = 0.8.25;

contract Test {
    bytes3 x = hex"AABBCC";
    bytes1 y = hex"BB";

    function test() public view {
        assert (x[1] == y);
    }
}
*)

lemma 
  shows "let pstorage = 
                ((\<lambda>_. undefined) 
                   (STR ''x'' := storage_data.Value (Bytes [CHR 0xAA, CHR 0xBB, CHR 0xCC])))
                   (STR ''y'' := storage_data.Value (Bytes [CHR 0xBB]));
            storage = (\<lambda>_. undefined) (A1 := pstorage);
            state = emptyState\<lparr>Storage := storage\<rparr>
         in is_Normal (execute (do {
              assert_monad (equals_monad (bytes_index_monad (contract_storeLookup (STR ''x'') []) (sint_monad 1)) (contract_storeLookup (STR ''y'') []))
            }) state)"
  by normalization

(*
pragma solidity = 0.8.25;

contract Test {
    bytes3 x = hex"AABBCC";
    bytes3 y = hex"AABBCC";

    function test() public view {
        assert (x == y);
    }
}
*)

lemma 
  shows "let pstorage = 
                ((\<lambda>_. undefined) 
                   (STR ''x'' := storage_data.Value (Bytes [CHR 0xAA, CHR 0xBB, CHR 0xCC])))
                   (STR ''y'' := storage_data.Value (Bytes [CHR 0xAA, CHR 0xBB, CHR 0xCC]));
            storage = (\<lambda>_. undefined) (A1 := pstorage);
            state = emptyState\<lparr>Storage := storage\<rparr>
         in is_Normal (execute (do {
              assert_monad (equals_monad (contract_storeLookup (STR ''x'') []) (contract_storeLookup (STR ''y'') []))
            }) state)"
  by normalization

(*
pragma solidity = 0.8.25;

contract Test {
    bytes3 x = hex"AABBCC";
    bytes4 y = hex"00AABBCC";

    function test() public view {
        assert (x == y);
    }
}
*)

lemma 
  shows "let pstorage = 
                ((\<lambda>_. undefined) 
                   (STR ''x'' := storage_data.Value (Bytes [CHR 0xAA, CHR 0xBB, CHR 0xCC])))
                   (STR ''y'' := storage_data.Value (Bytes [CHR 0x00, CHR 0xAA, CHR 0xBB, CHR 0xCC]));
            storage = (\<lambda>_. undefined) (A1 := pstorage);
            state = emptyState\<lparr>Storage := storage\<rparr>
         in is_Exception (execute (do {
              assert_monad (equals_monad (contract_storeLookup (STR ''x'') []) (contract_storeLookup (STR ''y'') []))
            }) state)"
  by normalization

(*
pragma solidity = 0.8.25;

contract Test {
    bytes3 x = hex"AABBCC";
    bytes4 y = hex"AABBCC00";

    function test() public view {
        assert (x == y);
    }
}
*)

lemma 
  shows "let pstorage = 
                ((\<lambda>_. undefined) 
                   (STR ''x'' := storage_data.Value (Bytes [CHR 0xAA, CHR 0xBB, CHR 0xCC])))
                   (STR ''y'' := storage_data.Value (Bytes [CHR 0xAA, CHR 0xBB, CHR 0xCC, CHR 0x00]));
            storage = (\<lambda>_. undefined) (A1 := pstorage);
            state = emptyState\<lparr>Storage := storage\<rparr>
         in is_Exception (execute (do {
              assert_monad (equals_monad (contract_storeLookup (STR ''x'') []) (contract_storeLookup (STR ''y'') []))
            }) state)"
  by normalization


(*
pragma solidity = 0.8.25;

contract Test {
    bytes3 x = hex"123456";
    bytes3 y = hex"F0874C";
    bytes3 z = hex"100444";

    function test() public view {
        assert (z == x & y);
    }
}
*)

lemma 
  shows "let pstorage = 
                (((\<lambda>_. undefined) 
                   (STR ''x'' := storage_data.Value (Bytes [CHR 0x12, CHR 0x34, CHR 0x56])))
                   (STR ''y'' := storage_data.Value (Bytes [CHR 0xF0, CHR 0x87, CHR 0x4C])))
                   (STR ''z'' := storage_data.Value (Bytes [CHR 0x10, CHR 0x04, CHR 0x44]));
            storage = (\<lambda>_. undefined) (A1 := pstorage);
            state = emptyState\<lparr>Storage := storage\<rparr>
         in is_Normal (execute (do {
              assert_monad (equals_monad (contract_storeLookup (STR ''z'') []) (bytes_and_monad (contract_storeLookup (STR ''x'') []) (contract_storeLookup (STR ''y'') [])))
            }) state)"
  by normalization

(*
pragma solidity = 0.8.25;

contract Test {
    bytes3 x = hex"123456";
    bytes3 y = hex"F0874C";
    bytes3 z = hex"F2B75E";

    function test() public view {
        assert (z == x | y);
    }
}
*)

context
  includes bit_operations_syntax
begin

lemma "word8_to_char ((char_to_word8 (CHR 0x56)) OR (char_to_word8 (CHR 0x4C))) = CHR 0x5E"
  by (normalization)
  
end

lemma 
  shows "let pstorage = 
                (((\<lambda>_. undefined)
                   (STR ''x'' := storage_data.Value (Bytes [CHR 0x12, CHR 0x34, CHR 0x56])))
                   (STR ''y'' := storage_data.Value (Bytes [CHR 0xF0, CHR 0x87, CHR 0x4C])))
                   (STR ''z'' := storage_data.Value (Bytes [CHR 0xF2, CHR 0xB7, CHR 0x5E]));
            storage = (\<lambda>_. undefined) (A1 := pstorage);
            state = emptyState\<lparr>Storage := storage\<rparr>
         in is_Normal (execute (do {
              assert_monad (equals_monad (contract_storeLookup (STR ''z'') []) (bytes_or_monad (contract_storeLookup (STR ''x'') []) (contract_storeLookup (STR ''y'') [])))
            }) state)"
  by normalization


(*
pragma solidity = 0.8.25;

contract Test {
    bytes3 x = hex"123456";
    bytes3 y = hex"F0874C";
    bytes3 z = hex"E2B31A";

    function test() public view {
        assert (z == x ^ y);
    }
}
*)


lemma 
  shows "let pstorage = 
                (((\<lambda>_. undefined)
                   (STR ''x'' := storage_data.Value (Bytes [CHR 0x12, CHR 0x34, CHR 0x56])))
                   (STR ''y'' := storage_data.Value (Bytes [CHR 0xF0, CHR 0x87, CHR 0x4C])))
                   (STR ''z'' := storage_data.Value (Bytes [CHR 0xE2, CHR 0xB3, CHR 0x1A]));
            storage = (\<lambda>_. undefined) (A1 := pstorage);
            state = emptyState\<lparr>Storage := storage\<rparr>
         in is_Normal (execute (do {
              assert_monad (equals_monad (contract_storeLookup (STR ''z'') []) (bytes_xor_monad (contract_storeLookup (STR ''x'') []) (contract_storeLookup (STR ''y'') [])))
            }) state)"
  by normalization

(*
  pragma solidity =0.8.25;

  contract Test {
      function test() public {
          bytes3 x;
          bytes3 y = hex"000000";
          assert(x == y);
      }
  }
*)

lemma "is_Normal (execute (do {
        decl (TBytes 3) (STR ''x'');
        write (adata.Value (Bytes [CHR 0x00, CHR 0x00, CHR 0x00])) (STR ''y'');
        assert_monad (equals_monad (contract_stackLookup (STR ''x'') []) (contract_stackLookup (STR ''y'') []))
      }) emptyState)" 
  by normalization


(*
  pragma solidity =0.8.25;

  contract Test {
      function test() public {
          bytes3 x = hex"123456";
          bytes4 y = hex"12345600"
          assert(bytes4(x) == y);
      }
  }
*)

lemma "is_Normal (execute (do {
        write (adata.Value (Bytes [CHR 0x12, CHR 0x34, CHR 0x56])) (STR ''x'');
        write (adata.Value (Bytes [CHR 0x12, CHR 0x34, CHR 0x56, CHR 0x00])) (STR ''y'');
        assert_monad (equals_monad (bytes_cast_monad 4 (contract_stackLookup (STR ''x'') [])) (contract_stackLookup (STR ''y'') []))
      }) emptyState)" 
  by normalization

(*
  pragma solidity =0.8.25;

  contract Test {
      function test() public {
          bytes3 x = hex"123456";
          bytes2 y = hex"1234"
          assert(bytes2(x) == y);
      }
  }
*)

lemma "is_Normal (execute (do {
        write (adata.Value (Bytes [CHR 0x12, CHR 0x34, CHR 0x56])) (STR ''x'');
        write (adata.Value (Bytes [CHR 0x12, CHR 0x34])) (STR ''y'');
        assert_monad (equals_monad (bytes_cast_monad 2 (contract_stackLookup (STR ''x'') [])) (contract_stackLookup (STR ''y'') []))
      }) emptyState)" 
  by normalization

lemma "is_Exception (execute (do {
         bytes_monad 1 []
      }) emptyState)"
  by normalization

lemma "is_Normal (execute (do {
         bytes_monad 32 (array 32 CHR 0x00)
      }) emptyState)"
  by normalization

lemma "is_Exception (execute (do {
         bytes_monad 33 (array 33 CHR 0x00)
      }) emptyState)"
  by normalization

end