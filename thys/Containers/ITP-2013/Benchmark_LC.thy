theory Benchmark_LC imports
  Benchmark_Comparison
  "../Set_Impl"
  "~~/src/HOL/Library/Code_Target_Nat"
begin

notepad begin
  have "complete 200 (12345, 67889) = (48, 50)"
    by eval
end

end
