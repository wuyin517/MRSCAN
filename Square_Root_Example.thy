theory Square_Root_Example
  imports Complex_Main
begin

(* 添加额外的导入语句，引入对 real 类型的排序约束 *)
instance real :: enum
  sorry

instance real :: equal
  by (intro_classes, simp add: equal_real_def)

(* 定义一个简单的函数，计算实数的平方根 *)
fun my_sqrt :: "real \<Rightarrow> real" where
  "my_sqrt x = sqrt x"

(* 示例：计算并显示平方根的输出 *)
value "my_sqrt 4"

end

end
