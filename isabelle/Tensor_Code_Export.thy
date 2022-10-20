
theory Tensor_Code_Export
  imports "Complex_Main" "HOL-Library.Code_Target_Int" "Tensor" "Tensor_Plus"
begin

typedef rtensor = "{t::nat list \<times> real list. length (snd t) = prod_list (fst t)}"
by (simp add: Ex_list_of_length)

definition rdims::"rtensor \<Rightarrow> nat list" where
  "rdims A = fst (Rep_rtensor A)"

definition rvec::"rtensor \<Rightarrow> real list" where
  "rvec A = snd (Rep_rtensor A)"

definition rtensor_from_vec::"nat list \<Rightarrow> real list \<Rightarrow> rtensor" where
  "rtensor_from_vec d v = Abs_rtensor (d,v)"


typedef rt = "UNIV::(real tensor) set"
  morphisms to_ten to_rt by simp

declare to_ten_inverse [simp]
    and to_rt_inverse [simp]

setup_lifting type_definition_rt

lift_definition vec :: "rt \<Rightarrow> real list" is "Tensor.vec" .

lift_definition dims :: "rt \<Rightarrow> nat list" is "Tensor.dims" .

lift_definition tensor_from_vec :: "nat list \<Rightarrow> real list \<Rightarrow> rt" is
  "Tensor.tensor_from_vec" .

code_printing
  type_constructor "rt" \<rightharpoonup>
    (OCaml) "Tensor.t"

fun a :: "rt \<Rightarrow> real list" where "a x = vec x"


fun r_add :: "rt \<Rightarrow> rt \<Rightarrow> rt" where "r_add x y = tensor_from_vec (dims x) (vec x)"

code_printing
  constant "r_add" \<rightharpoonup> (OCaml) "Tensor.add"

fun t :: "rt \<Rightarrow> rt \<Rightarrow> rt" where "t x y = r_add x y"

export_code t in OCaml module_name X

(**
definition r_add2 :: "real tensor \<Rightarrow> real tensor \<Rightarrow> real tensor" where "r_add2 x y = x + y"

code_printing
  constant "r_add2 :: real tensor \<Rightarrow> real tensor \<Rightarrow> real tensor" \<rightharpoonup>
    (OCaml) "rtensor.add"

export_code r_add2 in OCaml module_name Y**)

end